/*
  Copyright (c) 2026, MariaDB Foundation.
  Copyright (c) 2026, Roman Nozdrin <drrtuy@gmail.com>
  Copyright (c) 2026, Leonid Fedorov.

  This program is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; version 2 of the License.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1335 USA
*/

/*
  DuckDB scalar function overloads for MariaDB-compatible behavior.

  These add missing type overloads to DuckDB builtins so that pushdown
  queries from MariaDB work without SQL text rewriting.  Registered
  once at DuckdbManager::Initialize() via register_mysql_compat_functions().

  hex/oct/bin implementations ported from AliSQL's DuckDB fork.
*/

#include <my_global.h>
#include "log.h"

#undef UNKNOWN

#include "duckdb_mysql_compat.h"

#include "duckdb/catalog/catalog.hpp"
#include "duckdb/catalog/catalog_transaction.hpp"
#include "duckdb/common/bit_utils.hpp"
#include "duckdb/common/exception.hpp"
#include "duckdb/common/numeric_utils.hpp"
#include <cerrno>
#include <cstdlib>
#include "duckdb/common/string_util.hpp"
#include "duckdb/common/types.hpp"
#include "duckdb/common/types/blob.hpp"
#include "duckdb/common/vector_operations/unary_executor.hpp"
#include "duckdb/common/vector_operations/vector_operations.hpp"
#include "duckdb/function/scalar_function.hpp"
#include "duckdb/function/function_set.hpp"
#include "duckdb/parser/parsed_data/create_scalar_function_info.hpp"
#include "duckdb/common/types/timestamp.hpp"
#include "duckdb/common/types/date.hpp"
#include "duckdb/common/types/time.hpp"
#include "duckdb/main/database.hpp"
#include "duckdb/main/connection.hpp"

#include "duckdb/common/types/string_type.hpp"
#include "re2/re2.h"

/* ICU extension headers — used to honor the session TimeZone in
   TIMESTAMPTZ compat overloads (MariaDB TIMESTAMP columns are stored
   as TIMESTAMPTZ). The extension is statically built into the bundle. */
#include "icu-datefunc.hpp"
#include "unicode/ucal.h"

namespace myduck
{

/* ================================================================
   octet_length(VARCHAR) -> BIGINT
   DuckDB builtin only has octet_length(BLOB).
   MariaDB OCTET_LENGTH() works on any string type.
   ================================================================ */

static void octet_length_varchar_func(duckdb::DataChunk &args,
                                      duckdb::ExpressionState &state,
                                      duckdb::Vector &result)
{
  auto &input= args.data[0];
  auto count= args.size();

  duckdb::UnaryExecutor::Execute<duckdb::string_t, int64_t>(
      input, result, count,
      [](duckdb::string_t s) -> int64_t { return (int64_t) s.GetSize(); });
}

/* ================================================================
   length(VARCHAR) -> BIGINT  (byte count, MariaDB semantics)
   DuckDB builtin length(VARCHAR) returns character count.
   MariaDB LENGTH() = OCTET_LENGTH() = byte count.
   We override to match MariaDB behavior for pushdown queries.
   ================================================================ */

static void length_varchar_byte_func(duckdb::DataChunk &args,
                                     duckdb::ExpressionState &state,
                                     duckdb::Vector &result)
{
  duckdb::UnaryExecutor::Execute<duckdb::string_t, int64_t>(
      args.data[0], result, args.size(),
      [](duckdb::string_t s) -> int64_t { return (int64_t) s.GetSize(); });
}

/* ================================================================
   length(BLOB) -> BIGINT
   DuckDB builtin length() only works on VARCHAR (returns char count).
   MariaDB LENGTH() = OCTET_LENGTH() = byte count.
   ================================================================ */

/* ================================================================
   ascii(VARCHAR) -> INTEGER  (first byte, MariaDB semantics)
   DuckDB builtin ascii() returns Unicode codepoint of first character.
   MariaDB ASCII() returns the numeric value of the first byte.
   ================================================================ */

static void ascii_byte_func(duckdb::DataChunk &args,
                            duckdb::ExpressionState &state,
                            duckdb::Vector &result)
{
  duckdb::UnaryExecutor::Execute<duckdb::string_t, int32_t>(
      args.data[0], result, args.size(),
      [](duckdb::string_t s) -> int32_t {
        return s.GetSize() > 0 ? (unsigned char) s.GetData()[0] : 0;
      });
}

/* ================================================================
   ord(VARCHAR) -> BIGINT  (multibyte byte-value, MariaDB semantics)
   DuckDB builtin ord() returns Unicode codepoint.
   MariaDB ORD() for multibyte characters returns
   (byte1 * 256 + byte2) * 256 + byte3 ... etc.
   For single-byte characters, same as ASCII().
   ================================================================ */

static void ord_byte_func(duckdb::DataChunk &args,
                          duckdb::ExpressionState &state,
                          duckdb::Vector &result)
{
  duckdb::UnaryExecutor::Execute<duckdb::string_t, int32_t>(
      args.data[0], result, args.size(),
      [](duckdb::string_t s) -> int32_t {
        auto data= (const unsigned char *) s.GetData();
        auto size= s.GetSize();
        if (size == 0)
          return 0;
        /* Determine UTF-8 character length from first byte */
        unsigned char c= data[0];
        int char_len= 1;
        if (c >= 0xF0)
          char_len= 4;
        else if (c >= 0xE0)
          char_len= 3;
        else if (c >= 0xC0)
          char_len= 2;
        /* Single byte — same as ASCII */
        if (char_len == 1)
          return (int32_t) c;
        /* Multibyte: (b1 * 256 + b2) * 256 + b3 ... */
        int32_t val= 0;
        for (int i= 0; i < char_len && i < (int) size; i++)
          val= val * 256 + data[i];
        return val;
      });
}

/* ================================================================
   Helper: parse MariaDB time interval string 'D H:M:S.us' into
   microseconds. Supports formats:
     'HH:MM:SS', 'HH:MM:SS.uuuuuu', 'D HH:MM:SS', 'D HH:MM:SS.uuuuuu'
   Returns total microseconds. Negative values supported via leading '-'.
   ================================================================ */

static int64_t parse_mariadb_interval_us(const char *data, size_t len)
{
  if (len == 0)
    return 0;
  bool neg= false;
  size_t i= 0;
  if (data[0] == '-')
  {
    neg= true;
    i++;
  }
  int days= 0, hours= 0, minutes= 0, seconds= 0, usec= 0;

  /* Check if there's a 'D ' prefix (day followed by space) */
  size_t space= std::string(data + i, len - i).find(' ');
  if (space != std::string::npos)
  {
    days= atoi(std::string(data + i, space).c_str());
    i+= space + 1;
  }

  /* Parse H:M:S */
  int parts[3]= {0, 0, 0};
  int pidx= 0;
  size_t num_start= i;
  for (; i <= len && pidx < 3; i++)
  {
    if (i == len || data[i] == ':' || data[i] == '.')
    {
      parts[pidx++]= atoi(std::string(data + num_start, i - num_start).c_str());
      num_start= i + 1;
      if (i < len && data[i] == '.')
      {
        i++;
        break;
      }
    }
  }
  hours= parts[0];
  minutes= parts[1];
  seconds= parts[2];

  /* Parse fractional seconds */
  if (i < len)
  {
    std::string frac(data + i, len - i);
    /* Pad to 6 digits */
    while (frac.size() < 6)
      frac+= '0';
    frac= frac.substr(0, 6);
    usec= atoi(frac.c_str());
  }

  int64_t total_us= ((int64_t) days * 86400 + (int64_t) hours * 3600 +
                      (int64_t) minutes * 60 + seconds) *
                         1000000 +
                     usec;
  return neg ? -total_us : total_us;
}

/* ================================================================
   addtime(TIMESTAMP, VARCHAR) -> TIMESTAMP
   subtime(TIMESTAMP, VARCHAR) -> TIMESTAMP
   MariaDB ADDTIME/SUBTIME accepts time interval in 'D H:M:S.us' format.
   DuckDB INTERVAL doesn't parse this format.
   ================================================================ */

static void addtime_func(duckdb::DataChunk &args,
                         duckdb::ExpressionState &,
                         duckdb::Vector &result)
{
  duckdb::BinaryExecutor::Execute<duckdb::timestamp_t, duckdb::string_t,
                                  duckdb::timestamp_t>(
      args.data[0], args.data[1], result, args.size(),
      [](duckdb::timestamp_t ts, duckdb::string_t interval_str)
          -> duckdb::timestamp_t {
        int64_t us= parse_mariadb_interval_us(interval_str.GetData(),
                                              interval_str.GetSize());
        return duckdb::timestamp_t(ts.value + us);
      });
}

static void subtime_func(duckdb::DataChunk &args,
                         duckdb::ExpressionState &,
                         duckdb::Vector &result)
{
  duckdb::BinaryExecutor::Execute<duckdb::timestamp_t, duckdb::string_t,
                                  duckdb::timestamp_t>(
      args.data[0], args.data[1], result, args.size(),
      [](duckdb::timestamp_t ts, duckdb::string_t interval_str)
          -> duckdb::timestamp_t {
        int64_t us= parse_mariadb_interval_us(interval_str.GetData(),
                                              interval_str.GetSize());
        return duckdb::timestamp_t(ts.value - us);
      });
}

/* ================================================================
   rtrim(VARCHAR, VARCHAR), ltrim(VARCHAR, VARCHAR), trim(VARCHAR, VARCHAR)
   DuckDB builtins remove individual characters from the set.
   MariaDB TRIM removes a substring pattern (e.g. TRIM(TRAILING 'xyz' FROM s)
   removes the trailing "xyz" substring, not individual x/y/z chars).
   We override the 2-arg forms for substring semantics.
   ================================================================ */

static void rtrim_substr_func(duckdb::DataChunk &args,
                              duckdb::ExpressionState &,
                              duckdb::Vector &result)
{
  duckdb::BinaryExecutor::Execute<duckdb::string_t, duckdb::string_t,
                                  duckdb::string_t>(
      args.data[0], args.data[1], result, args.size(),
      [&](duckdb::string_t s, duckdb::string_t pat) -> duckdb::string_t {
        auto data= s.GetData();
        auto slen= (int64_t) s.GetSize();
        auto plen= (int64_t) pat.GetSize();
        if (plen == 0 || plen > slen)
          return s;
        /* Single char — same as DuckDB default behavior */
        if (plen == 1)
        {
          auto c= pat.GetData()[0];
          while (slen > 0 && data[slen - 1] == c)
            slen--;
          return duckdb::StringVector::AddString(result, data, slen);
        }
        /* Multi-char: remove trailing substring repeatedly */
        auto pdata= pat.GetData();
        while (slen >= plen &&
               memcmp(data + slen - plen, pdata, plen) == 0)
          slen-= plen;
        return duckdb::StringVector::AddString(result, data, slen);
      });
}

static void ltrim_substr_func(duckdb::DataChunk &args,
                              duckdb::ExpressionState &,
                              duckdb::Vector &result)
{
  duckdb::BinaryExecutor::Execute<duckdb::string_t, duckdb::string_t,
                                  duckdb::string_t>(
      args.data[0], args.data[1], result, args.size(),
      [&](duckdb::string_t s, duckdb::string_t pat) -> duckdb::string_t {
        auto data= s.GetData();
        auto slen= (int64_t) s.GetSize();
        auto plen= (int64_t) pat.GetSize();
        int64_t start= 0;
        if (plen == 0 || plen > slen)
          return s;
        if (plen == 1)
        {
          auto c= pat.GetData()[0];
          while (start < slen && data[start] == c)
            start++;
          return duckdb::StringVector::AddString(result, data + start,
                                                 slen - start);
        }
        auto pdata= pat.GetData();
        while (start + plen <= slen &&
               memcmp(data + start, pdata, plen) == 0)
          start+= plen;
        return duckdb::StringVector::AddString(result, data + start,
                                               slen - start);
      });
}

static void length_blob_func(duckdb::DataChunk &args,
                             duckdb::ExpressionState &state,
                             duckdb::Vector &result)
{
  auto &input= args.data[0];
  auto count= args.size();

  duckdb::UnaryExecutor::Execute<duckdb::string_t, int64_t>(
      input, result, count,
      [](duckdb::string_t s) -> int64_t { return (int64_t) s.GetSize(); });
}

/* ================================================================
   json_contains(json, candidate, path) -> BOOLEAN
   DuckDB has json_contains(json, candidate) -- 2-arg.
   MariaDB JSON_CONTAINS(json, candidate, path) -- 3-arg, extracts
   path first then checks containment.
   Implemented as: json_contains(json_extract(json, path), candidate)
   ================================================================ */

static void json_contains_3arg_func(duckdb::DataChunk &args,
                                    duckdb::ExpressionState &state,
                                    duckdb::Vector &result)
{
  auto &json_vec= args.data[0];
  auto &candidate_vec= args.data[1];
  auto &path_vec= args.data[2];
  auto count= args.size();

  duckdb::TernaryExecutor::Execute<duckdb::string_t, duckdb::string_t,
                                   duckdb::string_t, bool>(
      json_vec, candidate_vec, path_vec, result, count,
      [](duckdb::string_t json, duckdb::string_t candidate,
         duckdb::string_t path) -> bool {
        /* Minimal implementation: delegate to DuckDB's own functions
           would require a ClientContext which we don't have here.
           For now, return false -- placeholder for proper implementation. */
        (void) json;
        (void) candidate;
        (void) path;
        return false;
      });
}

/* ================================================================
   hex / oct / bin helper functions
   Ported from AliSQL's DuckDB fork (core_functions/scalar/string/hex.cpp).
   ================================================================ */

namespace {

using namespace duckdb;

/* ---- Hex byte writers ---- */

static void WriteHexBytes(uint64_t x, char *&output, idx_t buffer_size)
{
  idx_t offset= buffer_size * 4;
  for (; offset >= 4; offset -= 4)
  {
    uint8_t byte= (x >> (offset - 4)) & 0x0F;
    *output= Blob::HEX_TABLE[byte];
    output++;
  }
}

template <class T>
static void WriteHugeIntHexBytes(T x, char *&output, idx_t buffer_size)
{
  idx_t offset= buffer_size * 4;
  auto upper= x.upper;
  auto lower= x.lower;

  for (; offset >= 68; offset -= 4)
  {
    uint8_t byte= (upper >> (offset - 68)) & 0x0F;
    *output= Blob::HEX_TABLE[byte];
    output++;
  }

  for (; offset >= 4; offset -= 4)
  {
    uint8_t byte= (lower >> (offset - 4)) & 0x0F;
    *output= Blob::HEX_TABLE[byte];
    output++;
  }
}

/* ---- Binary (bin) byte writers ---- */

static void WriteBinBytes(uint64_t x, char *&output, idx_t buffer_size)
{
  idx_t offset= buffer_size;
  for (; offset >= 1; offset -= 1)
  {
    *output= NumericCast<char>(((x >> (offset - 1)) & 0x01) + '0');
    output++;
  }
}

template <class T>
static void WriteHugeIntBinBytes(T x, char *&output, idx_t buffer_size)
{
  auto upper= x.upper;
  auto lower= x.lower;
  idx_t offset= buffer_size;

  for (; offset >= 65; offset -= 1)
  {
    *output= ((upper >> (offset - 65)) & 0x01) + '0';
    output++;
  }

  for (; offset >= 1; offset -= 1)
  {
    *output= ((lower >> (offset - 1)) & 0x01) + '0';
    output++;
  }
}

/* ---- Octal byte writers ---- */

static void WriteOctBytes(uint64_t x, char *&output, idx_t buffer_size)
{
  idx_t offset= buffer_size * 3;
  for (; offset >= 3; offset -= 3)
  {
    uint8_t byte= (x >> (offset - 3)) & 0x07;
    *output= Blob::HEX_TABLE[byte];
    output++;
  }
}

template <class T>
static void WriteHugeIntOctBytes(T x, char *&output, idx_t buffer_size)
{
  idx_t offset= buffer_size * 3;
  auto upper= x.upper;
  auto lower= x.lower;

  for (; offset >= 69; offset -= 3)
  {
    uint8_t byte= (upper >> (offset - 66)) & 0x07;
    *output= Blob::HEX_TABLE[byte];
    output++;
  }

  {
    uint8_t byte= ((upper & 0x03) << 1) + ((lower >> offset) & 0x01);
    *output= Blob::HEX_TABLE[byte];
    output++;
    offset -= 3;
  }

  for (; offset >= 3; offset -= 3)
  {
    uint8_t byte= (lower >> (offset - 3)) & 0x07;
    *output= Blob::HEX_TABLE[byte];
    output++;
  }
}

/* ================================================================
   Hex operator structs
   ================================================================ */

struct HexStrOperator {
  template <class INPUT_TYPE, class RESULT_TYPE>
  static RESULT_TYPE Operation(INPUT_TYPE input, Vector &result)
  {
    auto data= input.GetData();
    auto size= input.GetSize();

    auto target= StringVector::EmptyString(result, size * 2);
    auto output= target.GetDataWriteable();

    for (idx_t i= 0; i < size; ++i)
    {
      *output= Blob::HEX_TABLE[(data[i] >> 4) & 0x0F];
      output++;
      *output= Blob::HEX_TABLE[data[i] & 0x0F];
      output++;
    }

    target.Finalize();
    return target;
  }
};

struct HexIntegralOperator {
  template <class INPUT_TYPE, class RESULT_TYPE>
  static RESULT_TYPE Operation(INPUT_TYPE input, Vector &result)
  {
    auto num_leading_zero=
        CountZeros<uint64_t>::Leading(static_cast<uint64_t>(input));
    idx_t num_bits_to_check= 64 - num_leading_zero;
    D_ASSERT(num_bits_to_check <= sizeof(INPUT_TYPE) * 8);

    idx_t buffer_size= (num_bits_to_check + 3) / 4;

    if (buffer_size == 0)
    {
      auto target= StringVector::EmptyString(result, 1);
      auto output= target.GetDataWriteable();
      *output= '0';
      target.Finalize();
      return target;
    }

    D_ASSERT(buffer_size > 0);
    auto target= StringVector::EmptyString(result, buffer_size);
    auto output= target.GetDataWriteable();

    WriteHexBytes(static_cast<uint64_t>(input), output, buffer_size);

    target.Finalize();
    return target;
  }
};

struct HexHugeIntOperator {
  template <class INPUT_TYPE, class RESULT_TYPE>
  static RESULT_TYPE Operation(INPUT_TYPE input, Vector &result)
  {
    idx_t num_leading_zero=
        CountZeros<hugeint_t>::Leading(UnsafeNumericCast<hugeint_t>(input));
    idx_t buffer_size= sizeof(INPUT_TYPE) * 2 - (num_leading_zero / 4);

    if (buffer_size == 0)
    {
      auto target= StringVector::EmptyString(result, 1);
      auto output= target.GetDataWriteable();
      *output= '0';
      target.Finalize();
      return target;
    }

    D_ASSERT(buffer_size > 0);
    auto target= StringVector::EmptyString(result, buffer_size);
    auto output= target.GetDataWriteable();

    WriteHugeIntHexBytes<hugeint_t>(input, output, buffer_size);

    target.Finalize();
    return target;
  }
};

struct HexUhugeIntOperator {
  template <class INPUT_TYPE, class RESULT_TYPE>
  static RESULT_TYPE Operation(INPUT_TYPE input, Vector &result)
  {
    idx_t num_leading_zero=
        CountZeros<uhugeint_t>::Leading(UnsafeNumericCast<uhugeint_t>(input));
    idx_t buffer_size= sizeof(INPUT_TYPE) * 2 - (num_leading_zero / 4);

    if (buffer_size == 0)
    {
      auto target= StringVector::EmptyString(result, 1);
      auto output= target.GetDataWriteable();
      *output= '0';
      target.Finalize();
      return target;
    }

    D_ASSERT(buffer_size > 0);
    auto target= StringVector::EmptyString(result, buffer_size);
    auto output= target.GetDataWriteable();

    WriteHugeIntHexBytes<uhugeint_t>(input, output, buffer_size);

    target.Finalize();
    return target;
  }
};

struct HexFloatOperator {
  template <class INPUT_TYPE, class RESULT_TYPE>
  static RESULT_TYPE Operation(INPUT_TYPE input, Vector &result)
  {
    int64_t input_integer= std::round(input);
    return HexIntegralOperator::Operation<int64_t, string_t>(input_integer,
                                                             result);
  }
};

/* ================================================================
   Oct operator structs
   ================================================================ */

struct OctIntegralOperator {
  template <class INPUT_TYPE, class RESULT_TYPE>
  static RESULT_TYPE Operation(INPUT_TYPE input, Vector &result)
  {
    auto num_leading_zero=
        CountZeros<uint64_t>::Leading(static_cast<uint64_t>(input));
    idx_t num_bits_to_check= 64 - num_leading_zero;
    D_ASSERT(num_bits_to_check <= sizeof(INPUT_TYPE) * 8);

    idx_t buffer_size= (num_bits_to_check + 2) / 3;

    if (buffer_size == 0)
    {
      auto target= StringVector::EmptyString(result, 1);
      auto output= target.GetDataWriteable();
      *output= '0';
      target.Finalize();
      return target;
    }

    D_ASSERT(buffer_size > 0);
    auto target= StringVector::EmptyString(result, buffer_size);
    auto output= target.GetDataWriteable();

    WriteOctBytes(static_cast<uint64_t>(input), output, buffer_size);

    target.Finalize();
    return target;
  }
};

struct OctHugeIntOperator {
  template <class INPUT_TYPE, class RESULT_TYPE>
  static RESULT_TYPE Operation(INPUT_TYPE input, Vector &result)
  {
    idx_t num_leading_zero=
        CountZeros<hugeint_t>::Leading(UnsafeNumericCast<hugeint_t>(input));
    idx_t buffer_size=
        (sizeof(INPUT_TYPE) * 2 - num_leading_zero + 2) / 3;

    if (buffer_size == 0)
    {
      auto target= StringVector::EmptyString(result, 1);
      auto output= target.GetDataWriteable();
      *output= '0';
      target.Finalize();
      return target;
    }

    D_ASSERT(buffer_size > 0);
    auto target= StringVector::EmptyString(result, buffer_size);
    auto output= target.GetDataWriteable();

    WriteHugeIntOctBytes<hugeint_t>(input, output, buffer_size);

    target.Finalize();
    return target;
  }
};

struct OctUhugeIntOperator {
  template <class INPUT_TYPE, class RESULT_TYPE>
  static RESULT_TYPE Operation(INPUT_TYPE input, Vector &result)
  {
    idx_t num_leading_zero=
        CountZeros<uhugeint_t>::Leading(UnsafeNumericCast<uhugeint_t>(input));
    idx_t buffer_size=
        (sizeof(INPUT_TYPE) * 2 - num_leading_zero + 2) / 3;

    if (buffer_size == 0)
    {
      auto target= StringVector::EmptyString(result, 1);
      auto output= target.GetDataWriteable();
      *output= '0';
      target.Finalize();
      return target;
    }

    D_ASSERT(buffer_size > 0);
    auto target= StringVector::EmptyString(result, buffer_size);
    auto output= target.GetDataWriteable();

    WriteHugeIntOctBytes<uhugeint_t>(input, output, buffer_size);

    target.Finalize();
    return target;
  }
};

struct OctFloatOperator {
  template <class INPUT_TYPE, class RESULT_TYPE>
  static RESULT_TYPE Operation(INPUT_TYPE input, Vector &result)
  {
    int64_t input_integer= std::round(input);
    return OctIntegralOperator::Operation<int64_t, string_t>(input_integer,
                                                             result);
  }
};

struct OctStrOperator {
  template <class INPUT_TYPE, class RESULT_TYPE>
  static RESULT_TYPE Operation(INPUT_TYPE input, Vector &result)
  {
    double d;
    std::string tmp(input.GetData(), input.GetSize());
    char *end= nullptr;
    errno= 0;
    d= strtod(tmp.c_str(), &end);
    bool success= (errno == 0 && end != tmp.c_str());
    if (!success)
    {
      auto target= StringVector::EmptyString(result, 1);
      auto output= target.GetDataWriteable();
      *output= '0';
      target.Finalize();
      return target;
    }
    else
    {
      return OctFloatOperator::Operation<double, RESULT_TYPE>(d, result);
    }
  }
};

/* ================================================================
   Bin (binary) operator structs
   ================================================================ */

struct BinaryIntegralOperator {
  template <class INPUT_TYPE, class RESULT_TYPE>
  static RESULT_TYPE Operation(INPUT_TYPE input, Vector &result)
  {
    auto num_leading_zero=
        CountZeros<uint64_t>::Leading(static_cast<uint64_t>(input));
    idx_t num_bits_to_check= 64 - num_leading_zero;
    D_ASSERT(num_bits_to_check <= sizeof(INPUT_TYPE) * 8);

    idx_t buffer_size= num_bits_to_check;

    if (buffer_size == 0)
    {
      auto target= StringVector::EmptyString(result, 1);
      auto output= target.GetDataWriteable();
      *output= '0';
      target.Finalize();
      return target;
    }

    D_ASSERT(buffer_size > 0);
    auto target= StringVector::EmptyString(result, buffer_size);
    auto output= target.GetDataWriteable();

    WriteBinBytes(static_cast<uint64_t>(input), output, buffer_size);

    target.Finalize();
    return target;
  }
};

struct BinaryHugeIntOperator {
  template <class INPUT_TYPE, class RESULT_TYPE>
  static RESULT_TYPE Operation(INPUT_TYPE input, Vector &result)
  {
    auto num_leading_zero=
        CountZeros<hugeint_t>::Leading(UnsafeNumericCast<hugeint_t>(input));
    idx_t buffer_size= sizeof(INPUT_TYPE) * 8 - num_leading_zero;

    if (buffer_size == 0)
    {
      auto target= StringVector::EmptyString(result, 1);
      auto output= target.GetDataWriteable();
      *output= '0';
      target.Finalize();
      return target;
    }

    auto target= StringVector::EmptyString(result, buffer_size);
    auto output= target.GetDataWriteable();

    WriteHugeIntBinBytes<hugeint_t>(input, output, buffer_size);

    target.Finalize();
    return target;
  }
};

struct BinaryUhugeIntOperator {
  template <class INPUT_TYPE, class RESULT_TYPE>
  static RESULT_TYPE Operation(INPUT_TYPE input, Vector &result)
  {
    auto num_leading_zero=
        CountZeros<uhugeint_t>::Leading(UnsafeNumericCast<uhugeint_t>(input));
    idx_t buffer_size= sizeof(INPUT_TYPE) * 8 - num_leading_zero;

    if (buffer_size == 0)
    {
      auto target= StringVector::EmptyString(result, 1);
      auto output= target.GetDataWriteable();
      *output= '0';
      target.Finalize();
      return target;
    }

    auto target= StringVector::EmptyString(result, buffer_size);
    auto output= target.GetDataWriteable();

    WriteHugeIntBinBytes<uhugeint_t>(input, output, buffer_size);

    target.Finalize();
    return target;
  }
};

struct BinaryFloatOperator {
  template <class INPUT_TYPE, class RESULT_TYPE>
  static RESULT_TYPE Operation(INPUT_TYPE input, Vector &result)
  {
    int64_t input_integer= std::round(input);
    return BinaryIntegralOperator::Operation<int64_t, string_t>(input_integer,
                                                                result);
  }
};

struct BinaryStrOperator {
  template <class INPUT_TYPE, class RESULT_TYPE>
  static RESULT_TYPE Operation(INPUT_TYPE input, Vector &result)
  {
    double d;
    std::string tmp(input.GetData(), input.GetSize());
    char *end= nullptr;
    errno= 0;
    d= strtod(tmp.c_str(), &end);
    bool success= (errno == 0 && end != tmp.c_str());
    if (!success)
    {
      auto target= StringVector::EmptyString(result, 1);
      auto output= target.GetDataWriteable();
      *output= '0';
      target.Finalize();
      return target;
    }
    else
    {
      return BinaryFloatOperator::Operation<double, RESULT_TYPE>(d, result);
    }
  }
};

/* ================================================================
   Template wrapper functions for UnaryExecutor::ExecuteString
   ================================================================ */

template <class INPUT, class OP>
static void ToHexFunction(DataChunk &args, ExpressionState &state,
                          Vector &result)
{
  D_ASSERT(args.ColumnCount() == 1);
  auto &input= args.data[0];
  idx_t count= args.size();
  UnaryExecutor::ExecuteString<INPUT, string_t, OP>(input, result, count);
}

template <class INPUT, class OP>
static void ToBinaryFunction(DataChunk &args, ExpressionState &state,
                             Vector &result)
{
  D_ASSERT(args.ColumnCount() == 1);
  auto &input= args.data[0];
  idx_t count= args.size();
  UnaryExecutor::ExecuteString<INPUT, string_t, OP>(input, result, count);
}

template <class INPUT, class OP>
static void ToOctFunction(DataChunk &args, ExpressionState &state,
                          Vector &result)
{
  D_ASSERT(args.ColumnCount() == 1);
  auto &input= args.data[0];
  idx_t count= args.size();
  UnaryExecutor::ExecuteString<INPUT, string_t, OP>(input, result, count);
}

} /* anonymous namespace */

/* ================================================================
   locate(substr, str) -> BIGINT
   locate(substr, str, pos) -> BIGINT
   MariaDB LOCATE(substr, str [, pos]) returns the position of the
   first occurrence of substr in str, starting at position pos (1-based).
   This is the reversed argument order of DuckDB's instr(str, substr).
   ================================================================ */

static void locate_2arg_func(duckdb::DataChunk &args,
                             duckdb::ExpressionState &state,
                             duckdb::Vector &result)
{
  auto &needle_vec= args.data[0];
  auto &haystack_vec= args.data[1];
  auto count= args.size();

  duckdb::BinaryExecutor::Execute<duckdb::string_t, duckdb::string_t,
                                  int64_t>(
      needle_vec, haystack_vec, result, count,
      [](duckdb::string_t needle, duckdb::string_t haystack) -> int64_t {
        if (needle.GetSize() == 0)
          return 1;
        auto haystack_data= haystack.GetData();
        auto haystack_size= haystack.GetSize();
        auto needle_data= needle.GetData();
        auto needle_size= needle.GetSize();

        if (needle_size > haystack_size)
          return 0;

        for (duckdb::idx_t i= 0; i <= haystack_size - needle_size; i++)
        {
          if (memcmp(haystack_data + i, needle_data, needle_size) == 0)
            return (int64_t)(i + 1);
        }
        return 0;
      });
}

static void locate_3arg_func(duckdb::DataChunk &args,
                             duckdb::ExpressionState &state,
                             duckdb::Vector &result)
{
  auto &needle_vec= args.data[0];
  auto &haystack_vec= args.data[1];
  auto &pos_vec= args.data[2];
  auto count= args.size();

  duckdb::TernaryExecutor::Execute<duckdb::string_t, duckdb::string_t,
                                   int64_t, int64_t>(
      needle_vec, haystack_vec, pos_vec, result, count,
      [](duckdb::string_t needle, duckdb::string_t haystack,
         int64_t pos) -> int64_t {
        if (pos < 1)
          return 0;
        if (needle.GetSize() == 0)
          return pos;

        auto haystack_data= haystack.GetData();
        auto haystack_size= (int64_t) haystack.GetSize();
        auto needle_data= needle.GetData();
        auto needle_size= (int64_t) needle.GetSize();

        /* pos is 1-based; convert to 0-based offset */
        int64_t start= pos - 1;
        if (start >= haystack_size)
          return 0;

        if (needle_size > haystack_size - start)
          return 0;

        for (int64_t i= start; i <= haystack_size - needle_size; i++)
        {
          if (memcmp(haystack_data + i, needle_data, needle_size) == 0)
            return i + 1;
        }
        return 0;
      });
}

/* ================================================================
   date_format(TIMESTAMP/DATE, VARCHAR) -> VARCHAR
   MariaDB DATE_FORMAT() uses MySQL format specifiers, which differ
   from the C-strftime specifiers of DuckDB's strftime() (e.g. %i vs
   %M for minutes, %M vs %B for month name), so the format string
   cannot be just pushed to DuckDB — we format natively with MariaDB
   semantics. Month/day names are English (lc_time_names=en_US, the 
   default).
   ================================================================ */

static const char *mysql_month_names[]= {
    "January", "February", "March",     "April",   "May",      "June",
    "July",    "August",   "September", "October", "November", "December"};

/* Indexed by ISO day of week - 1 (1=Monday .. 7=Sunday) */
static const char *mysql_day_names[]= {"Monday", "Tuesday",  "Wednesday",
                                       "Thursday", "Friday", "Saturday",
                                       "Sunday"};

static int32_t days_in_year(int32_t year)
{
  return duckdb::Date::IsLeapYear(year) ? 366 : 365;
}

/*
  Weekday index of a day number (days since 1970-01-01, a Thursday).
  Equivalent of MariaDB calc_weekday(): 0 = Sunday when sunday_first,
  0 = Monday otherwise.
*/
static uint32_t weekday_of(int64_t daynr, bool sunday_first)
{
  int64_t monday_idx= (daynr + 3) % 7; /* epoch day 0 -> 3 (Thursday) */
  if (monday_idx < 0)
    monday_idx+= 7;
  if (!sunday_first)
    return (uint32_t) monday_idx;
  return (uint32_t) ((monday_idx + 1) % 7);
}

/*
  Port of MariaDB calc_week() (sql/sql_time.cc) onto DuckDB dates.
  Flag combinations used by DATE_FORMAT (after MariaDB week_mode()
  normalization, which sets first_weekday for the Sunday-first modes):
    %U     : monday_first=0 week_year=0 first_weekday=1  (WEEK mode 0)
    %u     : monday_first=1 week_year=0 first_weekday=0  (WEEK mode 1)
    %V, %X : monday_first=0 week_year=1 first_weekday=1  (WEEK mode 2)
    %v, %x : monday_first=1 week_year=1 first_weekday=0  (WEEK mode 3)
*/
static uint32_t calc_week(duckdb::date_t d, bool monday_first, bool week_year,
                          bool first_weekday, int32_t &out_year)
{
  int32_t y, month, day;
  duckdb::Date::Convert(d, y, month, day);
  int64_t daynr= duckdb::Date::EpochDays(d);
  int64_t first_daynr=
      duckdb::Date::EpochDays(duckdb::Date::FromDate(y, 1, 1));
  uint32_t weekday= weekday_of(first_daynr, !monday_first);
  out_year= y;
  int64_t days;

  if (month == 1 && day <= (int32_t) (7 - weekday))
  {
    if (!week_year &&
        ((first_weekday && weekday != 0) || (!first_weekday && weekday >= 4)))
      return 0;
    week_year= true;
    out_year--;
    int32_t days_prev= days_in_year(out_year);
    first_daynr-= days_prev;
    weekday= (weekday + 53 * 7 - days_prev) % 7;
  }

  if ((first_weekday && weekday != 0) || (!first_weekday && weekday >= 4))
    days= daynr - (first_daynr + (7 - weekday));
  else
    days= daynr - (first_daynr - weekday);

  if (week_year && days >= 52 * 7)
  {
    weekday= (weekday + days_in_year(out_year)) % 7;
    if ((!first_weekday && weekday < 4) || (first_weekday && weekday == 0))
    {
      out_year++;
      return 1;
    }
  }
  return (uint32_t) (days / 7 + 1);
}

static void mysql_date_format(std::string &out, duckdb::date_t d,
                              duckdb::dtime_t t, const char *fmt,
                              size_t fmt_len)
{
  int32_t year, month, day;
  duckdb::Date::Convert(d, year, month, day);
  int32_t hour, minute, sec, micros;
  duckdb::Time::Convert(t, hour, minute, sec, micros);
  int32_t iso_dow= duckdb::Date::ExtractISODayOfTheWeek(d); /* 1=Mon..7=Sun */
  int32_t hour12= hour % 12;
  if (hour12 == 0) /* 0 and 12 o'clock both display as 12 on a 12-hour dial */
    hour12= 12;

  char buf[32];
  auto append= [&](const char *format, auto value) {
    snprintf(buf, sizeof(buf), format, value);
    out+= buf;
  };

  for (size_t i= 0; i < fmt_len; i++)
  {
    if (fmt[i] != '%' || i + 1 >= fmt_len)
    {
      out+= fmt[i];
      continue;
    }
    i++;
    int32_t week_year;
    switch (fmt[i])
    {
    case 'Y': append("%04d", year); break;
    case 'y': append("%02d", year % 100); break;
    case 'm': append("%02d", month); break;
    case 'c': append("%d", month); break;
    case 'd': append("%02d", day); break;
    case 'e': append("%d", day); break;
    case 'H': append("%02d", hour); break;
    case 'k': append("%d", hour); break;
    case 'h':
    case 'I': append("%02d", hour12); break;
    case 'l': append("%d", hour12); break;
    case 'i': append("%02d", minute); break;
    case 's':
    case 'S': append("%02d", sec); break;
    case 'f': append("%06d", micros); break;
    case 'p': out+= hour < 12 ? "AM" : "PM"; break;
    case 'r':
      snprintf(buf, sizeof(buf), "%02d:%02d:%02d %s", hour12, minute, sec,
               hour < 12 ? "AM" : "PM");
      out+= buf;
      break;
    case 'T':
      snprintf(buf, sizeof(buf), "%02d:%02d:%02d", hour, minute, sec);
      out+= buf;
      break;
    case 'M': out+= mysql_month_names[month - 1]; break;
    case 'b': out.append(mysql_month_names[month - 1], 3); break;
    case 'W': out+= mysql_day_names[iso_dow - 1]; break;
    case 'a': out.append(mysql_day_names[iso_dow - 1], 3); break;
    case 'j': append("%03d", duckdb::Date::ExtractDayOfTheYear(d)); break;
    case 'w': append("%d", iso_dow % 7); break; /* 0=Sunday..6=Saturday */
    case 'D':
      append("%d", day);
      if (day % 100 >= 11 && day % 100 <= 13)
        out+= "th";
      else
        switch (day % 10)
        {
        case 1: out+= "st"; break;
        case 2: out+= "nd"; break;
        case 3: out+= "rd"; break;
        default: out+= "th"; break;
        }
      break;
    case 'U': append("%02u", calc_week(d, false, false, true, week_year));
      break;
    case 'u': append("%02u", calc_week(d, true, false, false, week_year));
      break;
    case 'V': append("%02u", calc_week(d, false, true, true, week_year));
      break;
    case 'v': append("%02u", calc_week(d, true, true, false, week_year));
      break;
    case 'X':
      calc_week(d, false, true, true, week_year);
      append("%04d", week_year);
      break;
    case 'x':
      calc_week(d, true, true, false, week_year);
      append("%04d", week_year);
      break;
    case '%': out+= '%'; break;
    default: out+= fmt[i]; break; /* MariaDB drops the '%' */
    }
  }
}

static void date_format_ts_func(duckdb::DataChunk &args,
                                duckdb::ExpressionState &,
                                duckdb::Vector &result)
{
  duckdb::BinaryExecutor::Execute<duckdb::timestamp_t, duckdb::string_t,
                                  duckdb::string_t>(
      args.data[0], args.data[1], result, args.size(),
      [&](duckdb::timestamp_t ts, duckdb::string_t fmt) -> duckdb::string_t {
        duckdb::date_t d;
        duckdb::dtime_t t;
        duckdb::Timestamp::Convert(ts, d, t);
        std::string out;
        out.reserve(fmt.GetSize() + 16); // just reserve a little bit extra, as an optimization
        mysql_date_format(out, d, t, fmt.GetData(), fmt.GetSize());
        return duckdb::StringVector::AddString(result, out);
      });
}

static void date_format_date_func(duckdb::DataChunk &args,
                                  duckdb::ExpressionState &,
                                  duckdb::Vector &result)
{
  duckdb::BinaryExecutor::Execute<duckdb::date_t, duckdb::string_t,
                                  duckdb::string_t>(
      args.data[0], args.data[1], result, args.size(),
      [&](duckdb::date_t d, duckdb::string_t fmt) -> duckdb::string_t {
        std::string out;
        out.reserve(fmt.GetSize() + 16); // just reserve a little bit extra, as an optimization
        mysql_date_format(out, d, duckdb::dtime_t(0), fmt.GetData(),
                          fmt.GetSize());
        return duckdb::StringVector::AddString(result, out);
      });
}

/*
  date_format(TIMESTAMPTZ, VARCHAR): MariaDB TIMESTAMP columns are stored
  as TIMESTAMPTZ, and DuckDB has no implicit TIMESTAMPTZ -> TIMESTAMP cast
  for function binding. Mirror the ICU extension's own strftime: bind
  ICUDateFunc::BindData (captures the session TimeZone), then convert each
  instant to local wall-clock fields before formatting.
*/
static void date_format_tstz_func(duckdb::DataChunk &args,
                                  duckdb::ExpressionState &state,
                                  duckdb::Vector &result)
{
  using duckdb::ICUDateFunc;
  auto &func_expr= state.expr.Cast<duckdb::BoundFunctionExpression>();
  auto &info= func_expr.bind_info->Cast<ICUDateFunc::BindData>();
  duckdb::CalendarPtr calendar_ptr(info.calendar->clone());
  auto *calendar= calendar_ptr.get();

  duckdb::BinaryExecutor::Execute<duckdb::timestamp_t, duckdb::string_t,
                                  duckdb::string_t>(
      args.data[0], args.data[1], result, args.size(),
      [&](duckdb::timestamp_t ts, duckdb::string_t fmt) -> duckdb::string_t {
        uint64_t micros= ICUDateFunc::SetTime(calendar, ts);
        int32_t year= ICUDateFunc::ExtractField(calendar, UCAL_YEAR);
        int32_t month= ICUDateFunc::ExtractField(calendar, UCAL_MONTH) + 1;
        int32_t day= ICUDateFunc::ExtractField(calendar, UCAL_DATE);
        int32_t hour= ICUDateFunc::ExtractField(calendar, UCAL_HOUR_OF_DAY);
        int32_t minute= ICUDateFunc::ExtractField(calendar, UCAL_MINUTE);
        int32_t sec= ICUDateFunc::ExtractField(calendar, UCAL_SECOND);
        int32_t millis= ICUDateFunc::ExtractField(calendar, UCAL_MILLISECOND);
        duckdb::date_t d= duckdb::Date::FromDate(year, month, day);
        duckdb::dtime_t t= duckdb::Time::FromTime(
            hour, minute, sec, millis * 1000 + (int32_t) micros);
        std::string out;
        out.reserve(fmt.GetSize() + 16); // just reserve a little bit extra, as an optimization
        mysql_date_format(out, d, t, fmt.GetData(), fmt.GetSize());
        return duckdb::StringVector::AddString(result, out);
      });
}

/* ================================================================
   unix_timestamp(TIMESTAMPTZ) -> DOUBLE
   MariaDB UNIX_TIMESTAMP(ts) interprets ts in the session time zone.
   A TIMESTAMPTZ value is already epoch microseconds; naive TIMESTAMP
   and DATE arguments reach this overload through DuckDB's implicit
   cast, which applies the session TimeZone (ICU) — matching MariaDB.
   DOUBLE keeps microsecond precision exactly up to ~2^53 us (year
   2255); the server-side result field (INT or DECIMAL(,N) chosen by
   MariaDB from the argument's precision) does the final rounding.
   ================================================================ */

static void unix_timestamp_func(duckdb::DataChunk &args,
                                duckdb::ExpressionState &,
                                duckdb::Vector &result)
{
  duckdb::UnaryExecutor::Execute<duckdb::timestamp_t, double>(
      args.data[0], result, args.size(),
      [](duckdb::timestamp_t ts) -> double {
        return (double) ts.value / 1000000.0;
      });
}

/* ================================================================
   Registration
   ================================================================ */

void register_mysql_compat_functions(duckdb::DatabaseInstance &db)
{
  auto &catalog= duckdb::Catalog::GetSystemCatalog(db);
  auto transaction= duckdb::CatalogTransaction::GetSystemTransaction(db);

  /* octet_length(VARCHAR) -> BIGINT */
  {
    duckdb::ScalarFunctionSet set("octet_length");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::VARCHAR}, duckdb::LogicalType::BIGINT,
        octet_length_varchar_func));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* length(VARCHAR) -> BIGINT (byte count, replaces DuckDB char count) */
  /* length(BLOB) -> BIGINT */
  {
    duckdb::ScalarFunctionSet set("length");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::VARCHAR}, duckdb::LogicalType::BIGINT,
        length_varchar_byte_func));
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::BLOB}, duckdb::LogicalType::BIGINT,
        length_blob_func));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* ascii(VARCHAR) -> INTEGER (first byte, replaces DuckDB codepoint) */
  {
    duckdb::ScalarFunctionSet set("ascii");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::VARCHAR}, duckdb::LogicalType::INTEGER,
        ascii_byte_func));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* ord(VARCHAR) -> INTEGER (multibyte byte-value, replaces DuckDB codepoint) */
  {
    duckdb::ScalarFunctionSet set("ord");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::VARCHAR}, duckdb::LogicalType::INTEGER,
        ord_byte_func));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* json_contains(VARCHAR, VARCHAR, VARCHAR) -> BOOLEAN -- 3-arg */
  {
    duckdb::ScalarFunctionSet set("json_contains");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::VARCHAR, duckdb::LogicalType::VARCHAR,
         duckdb::LogicalType::VARCHAR},
        duckdb::LogicalType::BOOLEAN, json_contains_3arg_func));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* hex() -- full AliSQL-compatible overloads */
  {
    using namespace duckdb;
    ScalarFunctionSet set("hex");
    set.AddFunction(ScalarFunction(
        {LogicalType::VARCHAR}, LogicalType::VARCHAR,
        ToHexFunction<string_t, HexStrOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::BLOB}, LogicalType::VARCHAR,
        ToHexFunction<string_t, HexStrOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::BIGINT}, LogicalType::VARCHAR,
        ToHexFunction<int64_t, HexIntegralOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::UBIGINT}, LogicalType::VARCHAR,
        ToHexFunction<uint64_t, HexIntegralOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::HUGEINT}, LogicalType::VARCHAR,
        ToHexFunction<hugeint_t, HexHugeIntOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::UHUGEINT}, LogicalType::VARCHAR,
        ToHexFunction<uhugeint_t, HexUhugeIntOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::DOUBLE}, LogicalType::VARCHAR,
        ToHexFunction<double, HexFloatOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::FLOAT}, LogicalType::VARCHAR,
        ToHexFunction<float, HexFloatOperator>));
    CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* oct() -- full AliSQL-compatible overloads */
  {
    using namespace duckdb;
    ScalarFunctionSet set("oct");
    set.AddFunction(ScalarFunction(
        {LogicalType::VARCHAR}, LogicalType::VARCHAR,
        ToOctFunction<string_t, OctStrOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::BLOB}, LogicalType::VARCHAR,
        ToOctFunction<string_t, OctStrOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::BIGINT}, LogicalType::VARCHAR,
        ToOctFunction<int64_t, OctIntegralOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::UBIGINT}, LogicalType::VARCHAR,
        ToOctFunction<uint64_t, OctIntegralOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::HUGEINT}, LogicalType::VARCHAR,
        ToOctFunction<hugeint_t, OctHugeIntOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::UHUGEINT}, LogicalType::VARCHAR,
        ToOctFunction<uhugeint_t, OctUhugeIntOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::DOUBLE}, LogicalType::VARCHAR,
        ToOctFunction<double, OctFloatOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::FLOAT}, LogicalType::VARCHAR,
        ToOctFunction<float, OctFloatOperator>));
    CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* bin() -- full AliSQL-compatible overloads */
  {
    using namespace duckdb;
    ScalarFunctionSet set("bin");
    set.AddFunction(ScalarFunction(
        {LogicalType::VARCHAR}, LogicalType::VARCHAR,
        ToBinaryFunction<string_t, BinaryStrOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::BIGINT}, LogicalType::VARCHAR,
        ToBinaryFunction<int64_t, BinaryIntegralOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::UBIGINT}, LogicalType::VARCHAR,
        ToBinaryFunction<uint64_t, BinaryIntegralOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::HUGEINT}, LogicalType::VARCHAR,
        ToBinaryFunction<hugeint_t, BinaryHugeIntOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::UHUGEINT}, LogicalType::VARCHAR,
        ToBinaryFunction<uhugeint_t, BinaryUhugeIntOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::DOUBLE}, LogicalType::VARCHAR,
        ToBinaryFunction<double, BinaryFloatOperator>));
    set.AddFunction(ScalarFunction(
        {LogicalType::FLOAT}, LogicalType::VARCHAR,
        ToBinaryFunction<float, BinaryFloatOperator>));
    CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* locate(VARCHAR, VARCHAR) -> BIGINT  (2-arg) */
  /* locate(VARCHAR, VARCHAR, BIGINT) -> BIGINT  (3-arg) */
  {
    duckdb::ScalarFunctionSet set("locate");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::VARCHAR, duckdb::LogicalType::VARCHAR},
        duckdb::LogicalType::BIGINT, locate_2arg_func));
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::VARCHAR, duckdb::LogicalType::VARCHAR,
         duckdb::LogicalType::BIGINT},
        duckdb::LogicalType::BIGINT, locate_3arg_func));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* mid() — registered via SQL macro calling DuckDB's substr() which
     handles multibyte UTF-8 correctly. We use a dedicated connection
     for macro creation since macros support overloading by arg count
     only when created with different names — so we use one 3-arg macro
     that the 2-arg call will match via DuckDB's default parameter.
     Actually DuckDB substr already works as 2 or 3 arg. */
  {
    auto con= std::make_shared<duckdb::Connection>(db);
    con->Query("CREATE OR REPLACE MACRO mid(s, p, n := NULL) AS "
               "CASE WHEN n IS NULL THEN substr(s, p) "
               "ELSE substr(s, p, n) END");
  }

  /* regexp_instr(VARCHAR, VARCHAR) → INTEGER
     Returns 1-based position of first match, 0 if no match. */
  {
    duckdb::ScalarFunctionSet set("regexp_instr");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::VARCHAR, duckdb::LogicalType::VARCHAR},
        duckdb::LogicalType::INTEGER,
        [](duckdb::DataChunk &args, duckdb::ExpressionState &,
           duckdb::Vector &result) {
          duckdb::BinaryExecutor::Execute<duckdb::string_t, duckdb::string_t,
                                          int32_t>(
              args.data[0], args.data[1], result, args.size(),
              [](duckdb::string_t expr, duckdb::string_t pat) -> int32_t {
                duckdb_re2::RE2 re(
                    duckdb_re2::StringPiece(pat.GetData(), pat.GetSize()));
                if (!re.ok())
                  return 0;
                duckdb_re2::StringPiece match;
                duckdb_re2::StringPiece input(expr.GetData(), expr.GetSize());
                if (re.Match(input, 0, expr.GetSize(),
                             duckdb_re2::RE2::UNANCHORED, &match, 1))
                  return (int32_t)(match.data() - expr.GetData()) + 1;
                return 0;
              });
        }));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* regexp_replace(VARCHAR, VARCHAR, VARCHAR) → VARCHAR
     Replaces all occurrences of pattern in expr with replacement. */
  {
    duckdb::ScalarFunctionSet set("regexp_replace");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::VARCHAR, duckdb::LogicalType::VARCHAR,
         duckdb::LogicalType::VARCHAR},
        duckdb::LogicalType::VARCHAR,
        [](duckdb::DataChunk &args, duckdb::ExpressionState &,
           duckdb::Vector &result) {
          duckdb::TernaryExecutor::Execute<duckdb::string_t, duckdb::string_t,
                                           duckdb::string_t,
                                           duckdb::string_t>(
              args.data[0], args.data[1], args.data[2], result, args.size(),
              [&](duckdb::string_t expr, duckdb::string_t pat,
                  duckdb::string_t repl) -> duckdb::string_t {
                duckdb_re2::RE2 re(
                    duckdb_re2::StringPiece(pat.GetData(), pat.GetSize()));
                if (!re.ok())
                  return expr;
                std::string s(expr.GetData(), expr.GetSize());
                duckdb_re2::RE2::GlobalReplace(
                    &s,  re,
                    duckdb_re2::StringPiece(repl.GetData(), repl.GetSize()));
                return duckdb::StringVector::AddString(result, s);
              });
        }));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* regexp_substr(VARCHAR, VARCHAR) → VARCHAR
     Returns the substring matching pattern, or NULL if no match. */
  {
    duckdb::ScalarFunctionSet set("regexp_substr");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::VARCHAR, duckdb::LogicalType::VARCHAR},
        duckdb::LogicalType::VARCHAR,
        [](duckdb::DataChunk &args, duckdb::ExpressionState &,
           duckdb::Vector &result) {
          duckdb::BinaryExecutor::ExecuteWithNulls<duckdb::string_t,
                                                   duckdb::string_t,
                                                   duckdb::string_t>(
              args.data[0], args.data[1], result, args.size(),
              [&](duckdb::string_t expr, duckdb::string_t pat,
                  duckdb::ValidityMask &mask,
                  duckdb::idx_t idx) -> duckdb::string_t {
                duckdb_re2::RE2 re(
                    duckdb_re2::StringPiece(pat.GetData(), pat.GetSize()));
                if (!re.ok())
                {
                  mask.SetInvalid(idx);
                  return duckdb::string_t();
                }
                duckdb_re2::StringPiece match;
                duckdb_re2::StringPiece input(expr.GetData(), expr.GetSize());
                if (re.Match(input, 0, expr.GetSize(),
                             duckdb_re2::RE2::UNANCHORED, &match, 1))
                  return duckdb::StringVector::AddString(
                      result, match.data(), match.size());
                mask.SetInvalid(idx);
                return duckdb::string_t();
              });
        }));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* json_unquote(VARCHAR) → VARCHAR
     Removes JSON quotes and unescapes. Simple implementation. */
  {
    duckdb::ScalarFunctionSet set("json_unquote");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::VARCHAR}, duckdb::LogicalType::VARCHAR,
        [](duckdb::DataChunk &args, duckdb::ExpressionState &,
           duckdb::Vector &result) {
          duckdb::UnaryExecutor::Execute<duckdb::string_t, duckdb::string_t>(
              args.data[0], result, args.size(),
              [&](duckdb::string_t input) -> duckdb::string_t {
                auto data= input.GetData();
                auto size= input.GetSize();
                /* If not quoted, return as-is */
                if (size < 2 || data[0] != '"' || data[size - 1] != '"')
                  return input;
                /* Strip quotes and unescape */
                std::string out;
                out.reserve(size);
                for (size_t i= 1; i < size - 1; i++)
                {
                  if (data[i] == '\\' && i + 1 < size - 1)
                  {
                    i++;
                    switch (data[i])
                    {
                    case '"':  out+= '"'; break;
                    case '\\': out+= '\\'; break;
                    case '/':  out+= '/'; break;
                    case 'b':  out+= '\b'; break;
                    case 'f':  out+= '\f'; break;
                    case 'n':  out+= '\n'; break;
                    case 'r':  out+= '\r'; break;
                    case 't':  out+= '\t'; break;
                    default:   out+= '\\'; out+= data[i]; break;
                    }
                  }
                  else
                    out+= data[i];
                }
                return duckdb::StringVector::AddString(result, out);
              });
        }));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* addtime(TIMESTAMP/TIME, VARCHAR) → TIMESTAMP/TIME */
  {
    duckdb::ScalarFunctionSet set("addtime");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::TIMESTAMP, duckdb::LogicalType::VARCHAR},
        duckdb::LogicalType::TIMESTAMP, addtime_func));
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::TIME, duckdb::LogicalType::VARCHAR},
        duckdb::LogicalType::TIME,
        [](duckdb::DataChunk &args, duckdb::ExpressionState &,
           duckdb::Vector &result) {
          duckdb::BinaryExecutor::Execute<duckdb::dtime_t, duckdb::string_t,
                                          duckdb::dtime_t>(
              args.data[0], args.data[1], result, args.size(),
              [](duckdb::dtime_t t, duckdb::string_t s) -> duckdb::dtime_t {
                int64_t us= parse_mariadb_interval_us(s.GetData(),
                                                      s.GetSize());
                /* Wrap around 24h for DuckDB TIME range */
                int64_t r= t.micros + us;
                const int64_t day_us= 86400LL * 1000000;
                r= ((r % day_us) + day_us) % day_us;
                return duckdb::dtime_t(r);
              });
        }));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* subtime(TIMESTAMP/TIME, VARCHAR) → TIMESTAMP/TIME */
  {
    duckdb::ScalarFunctionSet set("subtime");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::TIMESTAMP, duckdb::LogicalType::VARCHAR},
        duckdb::LogicalType::TIMESTAMP, subtime_func));
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::TIME, duckdb::LogicalType::VARCHAR},
        duckdb::LogicalType::TIME,
        [](duckdb::DataChunk &args, duckdb::ExpressionState &,
           duckdb::Vector &result) {
          duckdb::BinaryExecutor::Execute<duckdb::dtime_t, duckdb::string_t,
                                          duckdb::dtime_t>(
              args.data[0], args.data[1], result, args.size(),
              [](duckdb::dtime_t t, duckdb::string_t s) -> duckdb::dtime_t {
                int64_t us= parse_mariadb_interval_us(s.GetData(),
                                                      s.GetSize());
                int64_t r= t.micros - us;
                const int64_t day_us= 86400LL * 1000000;
                r= ((r % day_us) + day_us) % day_us;
                return duckdb::dtime_t(r);
              });
        }));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* rtrim(VARCHAR, VARCHAR) — substring semantics (MariaDB TRIM) */
  {
    duckdb::ScalarFunctionSet set("rtrim");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::VARCHAR, duckdb::LogicalType::VARCHAR},
        duckdb::LogicalType::VARCHAR, rtrim_substr_func));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* ltrim(VARCHAR, VARCHAR) — substring semantics (MariaDB TRIM) */
  {
    duckdb::ScalarFunctionSet set("ltrim");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::VARCHAR, duckdb::LogicalType::VARCHAR},
        duckdb::LogicalType::VARCHAR, ltrim_substr_func));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* date_format(TIMESTAMP/DATE, VARCHAR) — MySQL format specifiers */
  {
    duckdb::ScalarFunctionSet set("date_format");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::TIMESTAMP, duckdb::LogicalType::VARCHAR},
        duckdb::LogicalType::VARCHAR, date_format_ts_func));
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::DATE, duckdb::LogicalType::VARCHAR},
        duckdb::LogicalType::VARCHAR, date_format_date_func));
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::TIMESTAMP_TZ, duckdb::LogicalType::VARCHAR},
        duckdb::LogicalType::VARCHAR, date_format_tstz_func,
        duckdb::ICUDateFunc::Bind));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  /* unix_timestamp(TIMESTAMPTZ) -> DOUBLE */
  {
    duckdb::ScalarFunctionSet set("unix_timestamp");
    set.AddFunction(duckdb::ScalarFunction(
        {duckdb::LogicalType::TIMESTAMP_TZ}, duckdb::LogicalType::DOUBLE,
        unix_timestamp_func));
    duckdb::CreateScalarFunctionInfo info(std::move(set));
    info.on_conflict= duckdb::OnCreateConflict::ALTER_ON_CONFLICT;
    catalog.CreateFunction(transaction, info);
  }

  sql_print_information(
      "DuckDB: registered MySQL-compatible function overloads "
      "(octet_length, length, ascii, ord, hex, oct, bin, locate, mid, "
      "rtrim, ltrim, regexp_instr, regexp_replace, regexp_substr, "
      "json_unquote, json_contains, date_format, unix_timestamp)");
}

} /* namespace myduck */
