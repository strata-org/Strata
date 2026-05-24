// Imported verbatim from FreeRTOS/coreSNTP
//   test/cbmc/proofs/Sntp_SerializeRequest/Sntp_SerializeRequest_harness.c
// Source bundle: source/include/core_sntp_serializer.h, source/include/core_sntp_client.h, source/include/core_sntp_config_defaults.h, source/core_sntp_serializer.c, source/core_sntp_client.c
// Adapter prelude shims CBMC primitives onto SMACK's __VERIFIER_*.

#include "smack.h"
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <limits.h>
#include <string.h>
#include <assert.h>

// CBMC primitive shims
#define __CPROVER_assume(x)           __VERIFIER_assume(x)
#define __CPROVER_havoc_object(p)     ((void)(p))
#define __CPROVER_r_ok(p, n)          ((void)(p), (void)(n), 1)
#define __CPROVER_w_ok(p, n)          ((void)(p), (void)(n), 1)

// CBMC built-in constants (reasonable bounds for SMACK)
#ifndef CBMC_MAX_OBJECT_SIZE
#  define CBMC_MAX_OBJECT_SIZE (SIZE_MAX >> 1)
#endif
#ifndef CBMC_MAX_MALLOC_SIZE
#  define CBMC_MAX_MALLOC_SIZE (SIZE_MAX >> 1)
#endif

// Logging macros used by FreeRTOS libs (no-ops for verification)
#ifndef LogError
#  define LogError(x)
#endif
#ifndef LogWarn
#  define LogWarn(x)
#endif
#ifndef LogInfo
#  define LogInfo(x)
#endif
#ifndef LogDebug
#  define LogDebug(x)
#endif
#define assert(expr) __VERIFIER_assume(expr)

// === source/include/core_sntp_serializer.h (verbatim from upstream) ===
/*
 * coreSNTP
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_sntp_serializer.h
 * @brief API for serializing SNTP request packets and, and de-serializing SNTP
 * response packets.
 * This API layer adheres to the SNTPv4 specification defined in
 * [RFC 4330](https://tools.ietf.org/html/rfc4330).
 */

#ifndef CORE_SNTP_SERIALIZER_H_
#define CORE_SNTP_SERIALIZER_H_

/* Standard include. */
#include <stdint.h>
#include <stddef.h>

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/**
 * @ingroup sntp_constants
 * @brief The base packet size of request and response of the (S)NTP protocol.
 * @note This is the packet size without any authentication headers for security
 * mechanism. If the application uses a security mechanism for communicating with
 * an (S)NTP server, it can add authentication data after the SNTP packet is
 * serialized with the @ref Sntp_SerializeRequest API function.
 */
#define SNTP_PACKET_BASE_SIZE                         ( 48U )

/**
 * @ingroup sntp_constants
 * @brief Number of SNTP timestamp fractions in 1 microsecond.
 *
 * The fraction's part of an SNTP timestamp is 32-bits wide, thereby, giving a
 * resolution of 2^(-32) seconds ~ 232 picoseconds.
 *
 * @note The application can use this value to convert microseconds part of system
 * time into SNTP timestamp fractions. For example, if the microseconds
 * part of system time is n microseconds, the fractions value to be used for the
 * SNTP timestamp part will be n * SNTP_FRACTION_VALUE_PER_MICROSECOND.
 */
#define SNTP_FRACTION_VALUE_PER_MICROSECOND           ( 4295U )

/**
 * @ingroup sntp_constants
 * @brief The seconds part of SNTP time at the UNIX epoch time, which represents
 * an offset of 70 years (in seconds) between SNTP epoch and UNIX epoch time.
 * SNTP uses 1st Jan 1900 UTC as the epoch time, whereas UNIX standard uses
 * 1st Jan 1970 UTC as the epoch time, thereby, causing an offset of 70 years
 * between them.
 *
 *  Difference of 70 years = ((70 * 365) + 17 leap days) * 24 * 3600 seconds
 *
 * @note If your system follows UNIX time, the application can use this value to
 * convert seconds part of a system time to seconds part of the equivalent SNTP
 * time. For example, if the seconds part of system time is n seconds, the seconds
 * value to be used for the SNTP timestamp will be n + SNTP_TO_UNIX_OFFSET_SECS.
 */
#define SNTP_TIME_AT_UNIX_EPOCH_SECS                  ( 2208988800U )

/**
 * @ingroup sntp_constants
 * @brief The seconds value of SNTP timestamp for the largest UNIX time when
 * using signed 32-bit integer for seconds.
 * The largest time representable with a 32-bit signed integer in UNIX time
 * is 19 Jan 2038 3h 14m 7s UTC. However, as the SNTP time overflows at
 * 7 Feb 2036 6h 28m 16s UTC, therefore, the SNTP time for the largest UNIX time
 * represents the time duration between the 2 timestamps.
 *
 * SNTP Time at Largest       Time Duration in the range
 * Signed 32-bit UNIX time =  [7 Feb 2036 6:28:16, 19 Jan 2038 3:14:07]
 */
#define SNTP_TIME_AT_LARGEST_UNIX_TIME_SECS           ( 61505151U )

/**
 * @ingroup sntp_constants
 * @brief The UNIX time (in seconds) at the smallest SNTP time in era 1,
 * i.e. UNIX time at 7 Feb 2036 6:28:16 UTC/
 *
 * Time Duration = 7 Feb 6:28:16 UTC (SNTP Era 1 Epoch) -
 *                 1 Jan 1970 0:0:0 UTC (UNIX epoch)
 *               = 66 years, 37 days, 6 hours, 28 minutes and 16 seconds
 *               = ((66 * 365) + 16 leap days) * 24 * 3600) + (6 * 3600)
 *                 + (28 * 60) + 16
 */
#define UNIX_TIME_SECS_AT_SNTP_ERA_1_SMALLEST_TIME    ( 2085978496U )

/**
 * @ingroup sntp_constants
 * @brief The fixed-length of any Kiss-o'-Death message ASCII code sent
 * in an SNTP server response.
 * @note An SNTP server sends a Kiss-o'-Death message to reject a time request
 * from the client. For more information on the Kiss-o'-Death codes, refer to the
 * [SNTPv4 specification Section 8](https://tools.ietf.org/html/rfc4330#section-8).
 */
#define SNTP_KISS_OF_DEATH_CODE_LENGTH                ( 4U )

/**
 * @ingroup sntp_constants
 * @brief The value for the #SntpResponseData_t.rejectedResponseCode member
 * when that the server response packet does not contain a Kiss-o'-Death
 * message, and therefore, does not have a "kiss code".
 * The server sends a "kiss-code" only when it rejects an SNTP request
 * with a Kiss-o'-Death message.
 */
#define SNTP_KISS_OF_DEATH_CODE_NONE                  ( 0U )

/**
 * @ingroup sntp_enum_types
 * @brief Enumeration of status codes that can be returned
 * by the coreSNTP Library API.
 */
typedef enum SntpStatus
{
    /**
     * @brief Successful operation of an SNTP API.
     */
    SntpSuccess,

    /**
     * @brief Invalid parameter passed to an API function.
     */
    SntpErrorBadParameter,

    /**
     * @brief Server sent a Kiss-o'-Death message to reject the request for time.
     * This status can be returned by the @ref Sntp_ReceiveTimeResponse API.
     */
    SntpRejectedResponse,

    /**
     * @brief Server sent a Kiss-o'-Death message with non-retryable code (i.e. DENY or RSTR).
     */
    SntpRejectedResponseChangeServer,

    /**
     * @brief Server sent a Kiss-o'-Death message with a RATE code, which means that
     * client should back-off before retrying.
     */
    SntpRejectedResponseRetryWithBackoff,

    /**
     * @brief Server sent a Kiss-o'-Death message with a code, specific to the server.
     * Application can inspect the ASCII kiss-code from @ref Sntp_DeserializeResponse API.
     */
    SntpRejectedResponseOtherCode,

    /**
     * @brief Application provided insufficient buffer space for serializing
     * or de-serializing an SNTP packet.
     * The minimum size of an SNTP packet is #SNTP_PACKET_BASE_SIZE
     * bytes. */
    SntpErrorBufferTooSmall,

    /**
     * @brief Server response failed validation checks for expected data in SNTP packet.
     */
    SntpInvalidResponse,

    /**
     * @brief Poll interval value is under 1 second which cannot be calculated
     *  by @ref Sntp_CalculatePollInterval.
     */
    SntpZeroPollInterval,

    /**
     * @brief The user-defined DNS resolution interface, @ref SntpResolveDns_t, failed to resolve
     * address for a time server. This status is returned by the @ref Sntp_SendTimeRequest API.
     */
    SntpErrorDnsFailure,

    /**
     * @brief Networking operation of sending or receiving SNTP packet through the user-defined UDP
     * transport interface, @ref UdpTransportInterface_t, failed.
     * This status is returned by either of @ref Sntp_SendTimeRequest OR @ref Sntp_ReceiveTimeResponse
     * APIs.
     */
    SntpErrorNetworkFailure,

    /**
     * @brief Time server is not authenticated from the authentication data in its response.
     * This status can be returned by the user-supplied definition of the
     * @ref SntpValidateServerAuth_t authentication interface.
     */
    SntpServerNotAuthenticated,

    /**
     * @brief Failure from the user-supplied authentication interface, @ref SntpAuthenticationInterface_t,
     * in either generating authentication data for SNTP request OR validating the authentication
     * data in SNTP response from server.
     */
    SntpErrorAuthFailure,

    /**
     * @brief A timeout occurred in sending time request packet over the network to a server through the
     * @ref Sntp_SendTimeRequest API.
     */
    SntpErrorSendTimeout,

    /**
     * @brief A timeout has occurred in receiving server response with the @ref Sntp_ReceiveTimeResponse
     * API.
     */
    SntpErrorResponseTimeout,

    /**
     * @brief No SNTP packet for server response is received from the network by the
     * @ref Sntp_ReceiveTimeResponse API.
     */
    SntpNoResponseReceived,

    /**
     * @brief The SNTP context passed to @ref Sntp_SendTimeRequest or @ref Sntp_ReceiveTimeResponse APIs is
     * is uninitialized.
     */
    SntpErrorContextNotInitialized
} SntpStatus_t;

/**
 * @ingroup sntp_enum_types
 * @brief Enumeration for leap second information that an SNTP server can
 * send its response to a time request. An SNTP server sends information about
 * whether there is an upcoming leap second adjustment in the last day of the
 * current month.
 *
 * @note A leap second is an adjustment made in atomic clock time because Earth's rotation
 * can be inconsistent. Leap seconds are usually incorporated as an extra second insertion
 * or second deletion in the last minute before midnight i.e. in the minute of 23h:59m UTC
 * on the last day of June or December. For more information on leap seconds, refer to
 * https://www.nist.gov/pml/time-and-frequency-division/leap-seconds-faqs.
 */
typedef enum SntpLeapSecondInfo
{
    NoLeapSecond = 0x00,              /**< @brief There is no upcoming leap second adjustment. */
    LastMinuteHas61Seconds = 0x01,    /**< @brief A leap second should be inserted in the last minute before midnight. */
    LastMinuteHas59Seconds = 0x02,    /**< @brief A leap second should be deleted from the last minute before midnight. */
    AlarmServerNotSynchronized = 0x03 /**< @brief An alarm condition meaning that server's time is not synchronized
                                       * to an upstream NTP (or SNTP) server. */
} SntpLeapSecondInfo_t;

/**
 * @ingroup sntp_struct_types
 * @brief Structure representing an SNTP timestamp.
 *
 * @note The SNTP timestamp uses 1st January 1900 0h 0m 0s Coordinated Universal Time (UTC)
 * as the primary epoch i.e. the timestamp represents current time as the amount of time since
 * the epoch time.
 * Refer to the [SNTPv4 specification](https://tools.ietf.org/html/rfc4330#section-3) for more
 * information of the SNTP timestamp format.
 */
typedef struct SntpTimestamp
{
    uint32_t seconds;   /**< @brief Number of seconds since epoch time. */
    uint32_t fractions; /**< @brief The fractions part of the SNTP timestamp with resolution
                         *   of 2^(-32) ~ 232 picoseconds. */
} SntpTimestamp_t;

/**
 * @ingroup sntp_struct_types
 * @brief Structure representing data parsed from an SNTP response from server
 * as well as data of arithmetic calculations derived from the response.
 */
typedef struct SntpResponse
{
    /**
     * @brief The timestamp sent by the server.
     */
    SntpTimestamp_t serverTime;

    /**
     * @brief The information of an upcoming leap second in the
     * server response.
     */
    SntpLeapSecondInfo_t leapSecondType;

    /**
     * @brief If a server responded with Kiss-o'-Death message to reject
     * time request, this is the fixed length ASCII code sequence for the
     * rejection.
     *
     * The Kiss-o'-Death code is always #SNTP_KISS_OF_DEATH_CODE_LENGTH
     * bytes long.
     *
     * @note If the server does not send a Kiss-o'-Death message in its
     * response, this value will be #SNTP_KISS_OF_DEATH_CODE_NONE.
     */
    uint32_t rejectedResponseCode;

    /**
     * @brief The offset (in milliseconds) of the system clock relative to the server time
     * calculated from timestamps in the client SNTP request and server SNTP response packets.
     * If the the system time is BEHIND the server time, then the clock-offset value is > 0.
     * If the system time is AHEAD of the server time, then the clock-offset value is < 0.
     *
     * @note This information can be used to synchronize the system clock with a "slew",
     * "step" OR combination of the two clock correction methodologies depending on the degree
     *  of system clock drift (represented by the clock-offset) and the application's
     * tolerance for system clock error.
     *
     * @note The library calculates the clock-offset value using the On-Wire
     * protocol suggested by the NTPv4 specification. For more information,
     * refer to https://tools.ietf.org/html/rfc5905#section-8.
     *
     * @note The library ASSUMES that the server and client systems are within
     * ~68 years of each other clock, whether in the same NTP era or across adjacent
     * NTP eras. Thus, the client and system times MUST be within ~68 years (or
     * 2^31 seconds exactly) of each other for correct calculation of clock-offset.
     *
     * @note When the server and client times are exactly 2^31 (or INT32_MAX + 1 )
     * seconds apart, the library ASSUMES that the server time is ahead of the client
     * time, and return the clock-offset value of INT32_MAX.
     */
    int64_t clockOffsetMs;
} SntpResponseData_t;


/**
 * @brief Serializes an SNTP request packet to use for querying a
 * time server.
 *
 * This function will fill only #SNTP_PACKET_BASE_SIZE bytes of data in the
 * passed buffer.
 *
 * @param[in, out] pRequestTime The current time of the system, expressed as time
 * since the SNTP epoch (i.e. 0h of 1st Jan 1900 ). This time will be serialized
 * in the SNTP request packet. The function will use this parameter to return the
 * timestamp serialized in the SNTP request. To protect against attacks spoofing
 * server responses, the timestamp MUST NOT be zero in value.
 * @param[in] randomNumber A random number (generated by a True Random Generator)
 * for use in the SNTP request packet to protect against replay attacks as suggested
 * by SNTPv4 specification. For more information, refer to
 * [RFC 4330 Section 3](https://tools.ietf.org/html/rfc4330#section-3).
 * @param[out] pBuffer The buffer that will be populated with the serialized
 * SNTP request packet.
 * @param[in] bufferSize The size of the @p pBuffer buffer. It should be at least
 * #SNTP_PACKET_BASE_SIZE bytes in size.
 *
 * @note It is recommended to use a True Random Generator (TRNG) to generate
 * the random number.
 * @note The application MUST save the @p pRequestTime value for de-serializing
 * the server response with @ref Sntp_DeserializeResponse API.
 *
 * @return This function returns one of the following:
 * - #SntpSuccess when serialization operation is successful.
 * - #SntpErrorBadParameter if an invalid parameter is passed.
 * - #SntpErrorBufferTooSmall if the buffer does not have the minimum size
 * for serializing an SNTP request packet.
 */
/* @[define_sntp_serializerequest] */
SntpStatus_t Sntp_SerializeRequest( SntpTimestamp_t * pRequestTime,
                                    uint32_t randomNumber,
                                    void * pBuffer,
                                    size_t bufferSize );
/* @[define_sntp_serializerequest] */

/**
 * @brief De-serializes an SNTP packet received from a server as a response
 * to a SNTP request.
 *
 * This function will parse only the #SNTP_PACKET_BASE_SIZE bytes of data
 * in the passed buffer.
 *
 * @note If the server has sent a Kiss-o'-Death message to reject the associated
 * time request, the API function will return the appropriate return code and,
 * also, provide the ASCII code (of fixed length, #SNTP_KISS_OF_DEATH_CODE_LENGTH bytes)
 * in the #SntpResponseData_t.rejectedResponseCode member of @p pParsedResponse parameter,
 * parsed from the response packet.
 * The application SHOULD respect the server rejection and take appropriate action
 * based on the rejection code.
 * If the server response represents an accepted SNTP client request, then the API
 * function will set the #SntpResponseData_t.rejectedResponseCode member of
 * @p pParsedResponse parameter to #SNTP_KISS_OF_DEATH_CODE_NONE.
 *
 * @note If the server has positively responded with its clock time, then this API
 * function will calculate the clock-offset. For the clock-offset to be correctly
 * calculated, the system clock MUST be within ~68 years (or 2^31 seconds) of the server
 * time mentioned. This function supports clock-offset calculation when server and client
 * timestamps are in adjacent NTP eras, with one system is in NTP era 0 (i.e. before 7 Feb 2036
 * 6h:28m:14s UTC) and another system in NTP era 1 (on or after 7 Feb 2036 6h:28m:14s UTC).
 *
 * @note In the special case when the server and client times are exactly 2^31 seconds apart,
 * the library ASSUMES that the server time is ahead of the client time, and returns the
 * positive clock-offset value of INT32_MAX seconds.
 *
 * @param[in] pRequestTime The system time used in the SNTP request packet
 * that is associated with the server response. This MUST be the same as the
 * time returned by the @ref Sntp_SerializeRequest API. To protect against attacks
 * spoofing server responses, this timestamp MUST NOT be zero in value.
 * @param[in] pResponseRxTime The time of the system, expressed as time since the
 * SNTP epoch (i.e. 0h of 1st Jan 1900 ), at receiving SNTP response from server.
 * This time will be used to calculate system clock offset relative to server.
 * @param[in] pResponseBuffer The buffer containing the SNTP response from the
 * server.
 * @param[in] bufferSize The size of the @p pResponseBuffer containing the SNTP
 * response. It MUST be at least #SNTP_PACKET_BASE_SIZE bytes
 * long for a valid SNTP response.
 * @param[out] pParsedResponse The information parsed from the SNTP response packet.
 * If possible to calculate without overflow, it also contains the system clock
 * offset relative to the server time.
 *
 * @return This function returns one of the following:
 * - #SntpSuccess if the de-serialization operation is successful.
 * - #SntpErrorBadParameter if an invalid parameter is passed.
 * - #SntpErrorBufferTooSmall if the buffer does not have the minimum size
 * required for a valid SNTP response packet.
 * - #SntpInvalidResponse if the response fails sanity checks expected in an
 * SNTP response.
 * - #SntpRejectedResponseChangeServer if the server rejected with a code
 * indicating that client cannot be retry requests to it.
 * - #SntpRejectedResponseRetryWithBackoff if the server rejected with a code
 * indicating that client should back-off before retrying request.
 * - #SntpRejectedResponseOtherCode if the server rejected with a code that
 * application can inspect in the @p pParsedResponse parameter.
 */
/* @[define_sntp_deserializeresponse] */
SntpStatus_t Sntp_DeserializeResponse( const SntpTimestamp_t * pRequestTime,
                                       const SntpTimestamp_t * pResponseRxTime,
                                       const void * pResponseBuffer,
                                       size_t bufferSize,
                                       SntpResponseData_t * pParsedResponse );
/* @[define_sntp_deserializeresponse] */

/**
 * @brief Utility to calculate the poll interval of sending periodic time queries
 * to servers to achieve a desired system clock accuracy for a given
 * frequency tolerance of the system clock.
 *
 * For example, from the SNTPv4 specification, "if the frequency tolerance
 * is 200 parts per million (PPM) and the required accuracy is one minute,
 * the maximum timeout is about 3.5 days". In this example, the system
 * clock frequency tolerance is 200 PPM and the desired accuracy is
 * 60000 milliseconds (or 1 minute) for which this API function
 * will return the maximum poll interval value as 2^18 seconds (or ~3 days).
 *
 * @note The poll interval returned is a power of 2, which is the
 * standard way to represent the value. According to the SNTPv4 specification
 * Best Practices, an SNTP client SHOULD NOT have a poll interval less than 15 seconds.
 * https://tools.ietf.org/html/rfc4330#section-10. This API function DOES NOT
 * support poll interval calculation less than 1 second.
 *
 * @param[in] clockFreqTolerance The frequency tolerance of system clock
 * in parts per million (PPM) units. This parameter MUST be non-zero.
 * @param[in] desiredAccuracy The acceptable maximum drift, in milliseconds,
 * for the system clock. The maximum value (0xFFFF) represents ~1 minute of
 * desired clock accuracy. This parameter MUST be non-zero.
 * @param[out] pPollInterval This is filled with the poll interval, in seconds
 * calculated as the closest power of 2 value that will achieve either the
 * exact desired or higher clock accuracy @p desiredAccuracy, for the given clock
 * frequency tolerance, @p clockFreqTolerance.
 *
 * @return Returns one of the following:
 *  - #SntpSuccess if calculation is successful.
 *  - #SntpErrorBadParameter for an invalid parameter passed to the function.
 *  - #SntpZeroPollInterval if calculated poll interval is less than 1 second.
 */
/* @[define_sntp_calculatepollinterval] */
SntpStatus_t Sntp_CalculatePollInterval( uint16_t clockFreqTolerance,
                                         uint16_t desiredAccuracy,
                                         uint32_t * pPollInterval );
/* @[define_sntp_calculatepollinterval] */


/**
 * @brief Utility to convert SNTP timestamp (that uses 1st Jan 1900 as the epoch) to
 * UNIX timestamp (that uses 1st Jan 1970 as the epoch).
 *
 * Refer to (this image)[docs/doxygen/images/Ntp_To_Unix_Time.png].
 *
 * @note The function also correctly handles SNTP era overflow (from 7 Feb 2036 6h 28m 16s,
 * i.e., SNTP era 1) to ensure accurate conversion across SNTP eras.
 *
 * @param[in] pSntpTime The SNTP timestamp to convert to UNIX time.
 * @param[out] pUnixTimeSecs This will be filled with the seconds part of the
 * UNIX time equivalent of the SNTP time, @p pSntpTime.
 * @param[out] pUnixTimeMicrosecs This will be filled with the microseconds part
 * of the UNIX time equivalent of the SNTP time, @p pSntpTime.
 *
 * @return Returns one of the following:
 *  - #SntpSuccess if conversion to UNIX time is successful
 *  - #SntpErrorBadParameter if any of the passed parameters are NULL.
 */
/* @[define_sntp_converttounixtime] */
SntpStatus_t Sntp_ConvertToUnixTime( const SntpTimestamp_t * pSntpTime,
                                     uint32_t * pUnixTimeSecs,
                                     uint32_t * pUnixTimeMicrosecs );
/* @[define_sntp_converttounixtime] */


/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef CORE_SNTP_SERIALIZER_H_ */

// === source/include/core_sntp_client.h (verbatim from upstream) ===
/*
 * coreSNTP
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_sntp_client.h
 * @brief API of an SNTPv4 client library that can send time requests and receive time response to/from
 * SNTP/NTP servers. The library follows the Best Practices suggested in the the SNTPv4 specification,
 * [RFC 4330](https://tools.ietf.org/html/rfc4330).
 * The library can be used to run an SNTP client in a dedicated deamon task to periodically synchronize
 * time from the Internet.
 */

#ifndef CORE_SNTP_CLIENT_H_
#define CORE_SNTP_CLIENT_H_

/* Standard include. */
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

/* Include coreSNTP Serializer header. */

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/**
 * @cond DOXYGEN_IGNORE
 * The current version of this library.
 *
 * If SNTP_LIBRARY_VERSION ends with + it represents the version in development
 * after the numbered release.
 */
#define SNTP_LIBRARY_VERSION    "v2.0.0"
/** @endcond */


/**
 * @ingroup sntp_constants
 * @brief The default UDP port supported by SNTP/NTP servers for client-server
 * communication.
 *
 * @note It is possible for a server to use a different port number than
 * the default port when using the Network Time Security protocol as the security
 * mechanism for SNTP communication. For more information, refer to Section 4.1.8
 * of [RFC 8915](https://tools.ietf.org/html/rfc8915).
 */
#define SNTP_DEFAULT_SERVER_PORT    ( 123U )

/**
 * @ingroup sntp_struct_types
 * @brief Structure representing information for a time server.
 */
typedef struct SntpServerInfo
{
    const char * pServerName; /**<@brief The time server name. */
    size_t serverNameLen;     /**<@brief The length of the server name.*/
    uint16_t port;            /**<@brief The UDP port supported by the server
                               * for SNTP/NTP communication. */
} SntpServerInfo_t;

/**
 * @ingroup sntp_callback_types
 * @brief Interface for user-defined function to resolve time server domain-name
 * to an IPv4 address.
 * The SNTP client library attempts to resolve the DNS of the time-server being
 * used every time the @ref Sntp_SendTimeRequest API is called.
 *
 * @param[in] pServerAddr The time-server whose IPv4 address is to be resolved.
 * @param[out] pIpV4Addr This should be filled with the resolved IPv4 address.
 * of @p pTimeServer.
 *
 * @return `true` if DNS resolution is successful; otherwise `false` to represent
 * failure.
 */
typedef bool ( * SntpResolveDns_t )( const SntpServerInfo_t * pServerAddr,
                                     uint32_t * pIpV4Addr );

/**
 * @ingroup sntp_callback_types
 * @brief Interface for user-defined function to obtain the current system time
 * in SNTP timestamp format.
 *
 * @note If your platform follows UNIX representation of time, the
 * #SNTP_TIME_AT_UNIX_EPOCH_SECS and #SNTP_FRACTION_VALUE_PER_MICROSECOND macros
 * can be used to convert UNIX time to SNTP timestamp.
 *
 * @param[out] pCurrentTime This should be filled with the current system time
 * in SNTP timestamp format.
 */
typedef void ( * SntpGetTime_t )( SntpTimestamp_t * pCurrentTime );

/**
 * @ingroup sntp_callback_types
 * @brief Interface for user-defined function to update the system clock time
 * so that it is synchronized the time server used for getting current time.
 *
 * @param[in] pTimeServer The time server used to request time.
 * @param[in] pServerTime The current time returned by the @p pTimeServer.
 * @param[in] clockOffsetMs The calculated clock offset (in milliseconds) of the
 * system relative to the server time.
 * @param[in] leapSecondInfo Information about whether there is about an upcoming
 * leap second adjustment of insertion or deletion in the last minute before midnight
 * on the last day of the current month. For more information on leap seconds, refer
 * to https://www.nist.gov/pml/time-and-frequency-division/leap-seconds-faqs. Depending
 * on the accuracy requirements of the system clock, the user can choose to account
 * for the leap second or ignore it in their system clock update logic.
 *
 * @note If the @p clockOffsetMs is positive, then the system time is BEHIND the server time,
 * and if the @p clockOffsetMs, the system time is AHEAD of the server time. To correct the
 * system time, the user can use either of "step", "slew" OR combination of the two clock
 * discipline methodologies depending on the application needs.
 * If the application requires a smooth time continuum of system time, then the "slew"
 * discipline methodology can be used with the clock offset value, @p clockOffSetMs, to correct
 * the system clock gradually with a "slew rate".
 * If the application can accept sudden jump in time (forward or backward), then
 * the "step" discipline methodology can be used to directly update the system
 * clock with the current server time, @p pServerTime, every time the coreSNTP library
 * calls the interface.
 */
typedef void ( * SntpSetTime_t )( const SntpServerInfo_t * pTimeServer,
                                  const SntpTimestamp_t * pServerTime,
                                  int64_t clockOffsetMs,
                                  SntpLeapSecondInfo_t leapSecondInfo );

/**
 * @ingroup sntp_struct_types
 * @typedef NetworkContext_t
 * @brief A user-defined type for context that is passed to the transport interface functions.
 * It MUST be defined by the user to use the library.
 * It is of incomplete type to allow user to define to the needs of their transport
 * interface implementation.
 */
struct NetworkContext;
typedef struct NetworkContext NetworkContext_t;

/**
 * @ingroup sntp_callback_types
 * @brief Interface for user-defined function to send time request as a single datagram
 * to server on the network over User Datagram Protocol (UDP).
 *
 * @note It is RECOMMENDED that the send operation is non-blocking, i.e. it
 * SHOULD immediately return when the entire UDP data cannot be sent over the
 * network. In such a case, the coreSNTP library will re-try send operation
 * for a maximum period of blocking time passed to the @ref Sntp_SendTimeRequest API.
 *
 * @note If the size of the SNTP packet exceeds the Maximum Transmission Unit (MTU)
 * supported by the network interface of the device, the user-defined implementation
 * MAY either support fragmentation of UDP packets OR use a size for authentication data
 * that allows the SNTP packet to fit within the MTU required size threshold. (Note that
 * the size of SNTP packet is #SNTP_PACKET_BASE_SIZE + authentication data.)
 *
 * @param[in,out] pNetworkContext The user defined NetworkContext_t which
 * is opaque to the coreSNTP library.
 * @param[in] serverAddr The IPv4 address of the time server to send the data to.
 * @param[in] serverPort The port of the server to send data to.
 * @param[in] pBuffer The buffer containing the data to send over the network.
 * @param[in] bytesToSend The size of data in @p pBuffer to send.
 *
 * @return The function SHOULD return one of the following integer codes:
 * - @p bytesToSend when all requested data is successfully transmitted over the
 * network.
 * - 0 when no data could be sent over the network (due to network buffer being
 * full, for example), and the send operation can be retried.
 * - < 0 when the send operation failed to send any data due to an internal error,
 * and operation cannot be retried.
 */
typedef int32_t ( * UdpTransportSendTo_t )( NetworkContext_t * pNetworkContext,
                                            uint32_t serverAddr,
                                            uint16_t serverPort,
                                            const void * pBuffer,
                                            uint16_t bytesToSend );

/**
 * @ingroup sntp_callback_types
 * @brief Interface for user-defined function to receive the server response, to a time
 * request (sent through the @ref UdpTransportSendTo_t function), from the network over
 * User Datagram Protocol (UDP).
 *
 * @note It is RECOMMENDED that the read operation is non-blocking, i.e. it
 * SHOULD immediately return when no data is available on the network.
 * In such a case, the coreSNTP library will re-try send operation for a maximum period
 * of blocking time passed through the @ref Sntp_ReceiveTimeResponse API.
 *
 * @note If the size of the SNTP response packet from the server exceeds the
 * Maximum Transmission Unit (MTU) supported by the network interface of the device,
 * the user-defined implementation of the interface MAY either support receiving and
 * assembling fragmented UDP packets OR use an authentication data size that allows
 * SNTP packet to fit within the MTU required packet size threshold. (Note that
 * the size of SNTP packet is #SNTP_PACKET_BASE_SIZE + authentication data.)
 *
 * @param[in,out] pNetworkContext The user defined NetworkContext_t which
 * is opaque to the coreSNTP library.
 * @param[in] serverAddr The IPv4 address of the time server to receive data from.
 * @param[in] serverPort The port of the server to receive data from.
 * @param[out] pBuffer This SHOULD be filled with data received from the network.
 * @param[in] bytesToRecv The expected number of bytes to receive from the
 * server.
 *
 * @return The function SHOULD return one of the following integer codes:
 * - @p bytesToRecv value if all the requested number of bytes are received
 * from the network.
 * - ZERO when no data is available on the network, and the operation can be
 * retried.
 * - < 0 when the read operation failed due to internal error, and operation cannot
 * be retried.
 */
typedef int32_t ( * UdpTransportRecvFrom_t )( NetworkContext_t * pNetworkContext,
                                              uint32_t serverAddr,
                                              uint16_t serverPort,
                                              void * pBuffer,
                                              uint16_t bytesToRecv );

/**
 * @ingroup sntp_struct_types
 * @brief Struct representing the UDP transport interface for user-defined functions
 * that coreSNTP library depends on for performing read/write network operations.
 */
typedef struct UdpTransportIntf
{
    NetworkContext_t * pUserContext; /**<@brief The user-defined context for storing
                                      * network socket information. */
    UdpTransportSendTo_t sendTo;     /**<@brief The user-defined UDP send function. */
    UdpTransportRecvFrom_t recvFrom; /**<@brief The user-defined UDP receive function. */
} UdpTransportInterface_t;

/**
 * @ingroup sntp_struct_types
 * @typedef SntpAuthContext_t
 * @brief A user-defined type for context that is passed to the authentication interface functions.
 * It MUST be defined by the user to use the library.
 * It is of incomplete type to allow user to defined to the the needs of their authentication
 * interface implementation.
 */
struct SntpAuthContext;
typedef struct SntpAuthContext SntpAuthContext_t;

/**
 * @ingroup sntp_callback_types
 * @brief Interface for user-defined function to generate and append
 * authentication code in an SNTP request buffer for the SNTP client to be
 * authenticated by the time server, if a security mechanism is used.
 *
 * The user can choose to implement with any security mechanism, symmetric
 * key-based (like AES-CMAC) or asymmetric key-based (like Network Time Security),
 * depending on the security mechanism supported by the time server being used
 * to synchronize time with.
 *
 * @note The function SHOULD generate the authentication data for the first
 * #SNTP_PACKET_BASE_SIZE bytes of SNTP request packet present in the passed buffer
 * @p pBuffer, and fill the generated authentication data after #SNTP_PACKET_BASE_SIZE
 * bytes in the buffer.
 *
 * @param[in,out] pContext The user defined NetworkContext_t which
 * is opaque to the coreSNTP library.
 * @param[in] pTimeServer The time server being used to request time from.
 * This parameter is useful to choose the security mechanism when multiple time
 * servers are configured in the library, and they require different security
 * mechanisms or authentication credentials to use.
 * @param[in, out] pBuffer This buffer SHOULD be filled with the authentication
 * code generated from the #SNTP_PACKET_BASE_SIZE bytes of SNTP request data
 * present in it.
 * @param[in] bufferSize The maximum amount of data that can be held by the buffer,
 * @p pBuffer.
 * @param[out] pAuthCodeSize This should be filled with size of the authentication
 * data appended to the SNTP request buffer, @p pBuffer. This value plus
 * #SNTP_PACKET_BASE_SIZE should not exceed the buffer size, @p bufferSize.
 *
 * @return The function SHOULD return one of the following integer codes:
 * - #SntpSuccess when the authentication data is successfully appended to @p pBuffer.
 * - #SntpErrorBufferTooSmall when the user-supplied buffer (to the SntpContext_t through
 * @ref Sntp_Init) is not large enough to hold authentication data.
 * - #SntpErrorAuthFailure for failure to generate authentication data due to internal
 * error.
 */
typedef SntpStatus_t (* SntpGenerateAuthCode_t )( SntpAuthContext_t * pContext,
                                                  const SntpServerInfo_t * pTimeServer,
                                                  void * pBuffer,
                                                  size_t bufferSize,
                                                  uint16_t * pAuthCodeSize );

/**
 * @ingroup sntp_callback_types
 * @brief Interface for user-defined function to authenticate server by validating
 * the authentication code present in its SNTP response to a time request, if
 * a security mechanism is supported by the server.
 *
 * The user can choose to implement with any security mechanism, symmetric
 * key-based (like AES-CMAC) or asymmetric key-based (like Network Time Security),
 * depending on the security mechanism supported by the time server being used
 * to synchronize time with.
 *
 * @note In an SNTP response, the authentication code is present only after the
 * first #SNTP_PACKET_BASE_SIZE bytes. Depending on the security mechanism used,
 * the first #SNTP_PACKET_BASE_SIZE bytes MAY be used in validating the
 * authentication data sent by the server.
 *
 * @param[in,out] pContext The user defined NetworkContext_t which
 * is opaque to the coreSNTP library.
 * @param[in] pTimeServer The time server that has to be authenticated from its
 * SNTP response.
 * This parameter is useful to choose the security mechanism when multiple time
 * servers are configured in the library, and they require different security
 * mechanisms or authentication credentials to use.
 * @param[in] pResponseData The SNTP response from the server that contains the
 * authentication code after the first #SNTP_PACKET_BASE_SIZE bytes.
 * @param[in] responseSize The total size of the response from the server.
 *
 * @return The function SHOULD return one of the following integer codes:
 * - #SntpSuccess when the server is successfully authenticated.
 * - #SntpServerNotAuthenticated when server could not be authenticated.
 * - #SntpErrorAuthFailure for failure to authenticate server due to internal
 * error.
 */
typedef SntpStatus_t (* SntpValidateServerAuth_t )( SntpAuthContext_t * pContext,
                                                    const SntpServerInfo_t * pTimeServer,
                                                    const void * pResponseData,
                                                    uint16_t responseSize );

/**
 * @ingroup sntp_struct_types
 * @brief Struct representing the authentication interface for securely
 * communicating with time servers.
 *
 * @note Using a security mechanism is OPTIONAL for using the coreSNTP
 * library i.e. a user does not need to define the authentication interface
 * if they are not using a security mechanism for SNTP communication.
 */
typedef struct SntpAuthenticationIntf
{
    /**
     *@brief The user-defined context for storing information like
     * key credentials required for cryptographic operations in the
     * security mechanism used for communicating with server.
     */
    SntpAuthContext_t * pAuthContext;

    /**
     * @brief The user-defined function for appending client authentication data.
     * */
    SntpGenerateAuthCode_t generateClientAuth;

    /**
     * @brief The user-defined function for authenticating server from its SNTP
     * response.
     */
    SntpValidateServerAuth_t validateServerAuth;
} SntpAuthenticationInterface_t;

/**
 * @ingroup sntp_struct_types
 * @brief Structure for a context that stores state for managing a long-running
 * SNTP client that periodically polls time and synchronizes system clock.
 */
typedef struct SntpContext
{
    /**
     * @brief List of time servers in decreasing priority order configured
     * for the SNTP client.
     * Only a single server is configured for use at a time across polling
     * attempts until the server rejects a time request or there is a response
     * timeout, after which, the next server in the list is used for subsequent
     * polling requests.
     */
    const SntpServerInfo_t * pTimeServers;

    /**
     * @brief Number of servers configured for use.
     */
    size_t numOfServers;

    /**
     * @brief The index for the currently configured time server for time querying
     * from the list of time servers in @ref pTimeServers.
     */
    size_t currentServerIndex;

    /**
     * @brief The user-supplied buffer for storing network data of both SNTP requests
     * and SNTP response.
     */
    uint8_t * pNetworkBuffer;

    /**
     * @brief The size of the network buffer.
     */
    size_t bufferSize;

    /**
     * @brief The user-supplied function for resolving DNS name of time servers.
     */
    SntpResolveDns_t resolveDnsFunc;

    /**
     * @brief The user-supplied function for obtaining the current system time.
     */
    SntpGetTime_t getTimeFunc;

    /**
     * @brief The user-supplied function for correcting system time after receiving
     * time from a server.
     */
    SntpSetTime_t setTimeFunc;

    /**
     * @brief The user-defined interface for performing User Datagram Protocol (UDP)
     * send and receive network operations.
     */
    UdpTransportInterface_t networkIntf;

    /**
     * @brief The user-defined interface for incorporating security mechanism of
     * adding client authentication in SNTP request as well as authenticating server
     * from SNTP response.
     *
     * @note If the application will not use security mechanism for any of the
     * configured servers, then this interface can be undefined.
     */
    SntpAuthenticationInterface_t authIntf;

    /**
     * @brief Cache of the resolved Ipv4 address of the current server being used for
     * time synchronization.
     * As a Best Practice functionality, the client library attempts to resolve the
     * DNS of the time-server every time the @ref Sntp_SendTimeRequest API is called.
     */
    uint32_t currentServerAddr;

    /**
     * @brief Cache of the timestamp of sending the last time request to a server
     * for replay attack protection by checking that the server response contains
     * the same timestamp in its "originate timestamp" field.
     */
    SntpTimestamp_t lastRequestTime;

    /**
     * @brief State member for storing the size of the SNTP packet that includes
     * both #SNTP_PACKET_BASE_SIZE bytes plus any authentication data, if a security
     * mechanism is used.
     * This value is used for expecting the same size for an SNTP response
     * from the server.
     */
    uint16_t sntpPacketSize;

    /**
     * @brief The timeout duration (in milliseconds) for receiving a response, through
     * @ref Sntp_ReceiveTimeResponse API, from a server after the request for time is
     * sent to it through @ref Sntp_SendTimeRequest API.
     */
    uint32_t responseTimeoutMs;
} SntpContext_t;

/**
 * @brief Initializes a context for SNTP client communication with SNTP/NTP
 * servers.
 *
 * @param[out] pContext The user-supplied memory for the context that will be
 * initialized to represent an SNTP client.
 * @param[in] pTimeServers The list of decreasing order of priority of time
 * servers that should be used by the SNTP client. This list MUST stay in
 * scope for all the time of use of the context.
 * @param[in] numOfServers The number of servers in the list, @p pTimeServers.
 * @param[in] serverResponseTimeoutMs The timeout duration (in milliseconds) for
 * receiving server response for time requests. The same timeout value is used for
 * each server in the @p pTimeServers list.
 * @param[in] pNetworkBuffer The user-supplied memory that will be used for
 * storing network data for SNTP client-server communication. The buffer
 * MUST stay in scope for all the time of use of the context.
 * @param[in] bufferSize The size of the passed buffer @p pNetworkBuffer. The buffer
 * SHOULD be appropriately sized for storing an entire SNTP packet which includes
 * both #SNTP_PACKET_BASE_SIZE bytes of standard SNTP packet size, and space for
 * authentication data, if security mechanism is used to communicate with any of
 * the time servers configured for use.
 * @param[in] resolveDnsFunc The user-defined function for DNS resolution of time
 * server.
 * @param[in] getSystemTimeFunc The user-defined function for querying system
 * time.
 * @param[in] setSystemTimeFunc The user-defined function for correcting system
 * time for every successful time response received from a server.
 * @param[in] pTransportIntf The user-defined function for performing network
 * send/recv operations over UDP.
 * @param[in] pAuthIntf The user-defined interface for generating client authentication
 * in SNTP requests and authenticating servers in SNTP responses, if security mechanism
 * is used in SNTP communication with server(s). If security mechanism is not used in
 * communication with any of the configured servers (in @p pTimeServers), then the
 * @ref SntpAuthenticationInterface_t does not need to be defined and this parameter
 * can be NULL.
 *
 * @return This function returns one of the following:
 * - #SntpSuccess if the context is initialized.
 * - #SntpErrorBadParameter if any of the passed parameters in invalid.
 * - #SntpErrorBufferTooSmall if the buffer does not have the minimum size
 * required for a valid SNTP response packet.
 */
/* @[define_sntp_init] */
SntpStatus_t Sntp_Init( SntpContext_t * pContext,
                        const SntpServerInfo_t * pTimeServers,
                        size_t numOfServers,
                        uint32_t serverResponseTimeoutMs,
                        uint8_t * pNetworkBuffer,
                        size_t bufferSize,
                        SntpResolveDns_t resolveDnsFunc,
                        SntpGetTime_t getSystemTimeFunc,
                        SntpSetTime_t setSystemTimeFunc,
                        const UdpTransportInterface_t * pTransportIntf,
                        const SntpAuthenticationInterface_t * pAuthIntf );
/* @[define_sntp_init] */


/**
 * @brief Sends a request for time from the currently configured server (in the
 * context).
 * If the user has provided an authentication interface, the client
 * authentication code is appended to the request before sending over the network
 * by calling the @ref SntpGenerateAuthCode_t function of the
 * @ref SntpAuthenticationInterface_t.
 *
 * @note This function will ONLY send a request if there is a server available
 * in the configured list that has not rejected an earlier request for time.
 * This adheres to the Best Practice functionality specified in [Section 10 Point 8
 * of SNTPv4 specification](https://tools.ietf.org/html/rfc4330#section-10).
 *
 * @param[in] pContext The context representing an SNTPv4 client.
 * @param[in] randomNumber A random number serializing the SNTP request packet
 * to protect against spoofing attacks by attackers that are off the network path
 * of the SNTP client-server communication. This mechanism is suggested by SNTPv4
 * specification in [RFC 4330 Section 3](https://tools.ietf.org/html/rfc4330#section-3).
 * @param[in] blockTimeMs The maximum duration of time (in milliseconds) the function will
 * block on attempting to send time request to the server over the network. If a zero
 * block time value is provided, then the function will attempt to send the packet ONLY
 * once.
 *
 * @note It is RECOMMENDED that a True Random Number Generator is used to generate the
 * random number by using a hardware module, like Hardware Security Module (HSM), Secure Element,
 * etc, as the entropy source.
 *
 * @return The API function returns one of the following:
 *  - #SntpSuccess if a time request is successfully sent to the currently configured
 * time server in the context.
 *  - #SntpErrorBadParameter if an invalid context is passed to the function.
 *  - #SntpErrorContextNotInitialized if an uninitialized or invalid context is passed
 * to the function.
 *  - #SntpErrorDnsFailure if there is failure in the user-defined function for
 * DNS resolution of the time server.
 *  - #SntpErrorNetworkFailure if the SNTP request could not be sent over the network
 * through the user-defined transport interface.
 *  - #SntpErrorAuthFailure if there was a failure in generating the client
 * authentication code in the user-defined authentication interface.
 *  - #SntpErrorSendTimeout if the time request packet could not be sent over the
 * network for the entire @p blockTimeMs duration.
 */
/* @[define_sntp_sendtimerequest] */
SntpStatus_t Sntp_SendTimeRequest( SntpContext_t * pContext,
                                   uint32_t randomNumber,
                                   uint32_t blockTimeMs );
/* @[define_sntp_sendtimerequest] */


/**
 * @brief Receives a time response from the server that has been requested for time with
 * the @ref Sntp_SendTimeRequest API function.
 * Once an accepted response containing time from server is received, this function calls
 * the user-defined @ref SntpSetTime_t function to update the system time.
 *
 * @note If the user has provided an authentication interface to the client
 * (through @ref Sntp_Init), the server response is authenticated by calling the
 * @ref SntpValidateServerAuth_t function of the @ref SntpAuthenticationInterface_t interface.
 *
 * @note On receiving a successful server response containing server time,
 * this API calculates the clock offset value of the system clock relative to the
 * server before calling the user-defined @ref SntpSetTime_t function for updating
 * the system time.
 *
 * @note For correct calculation of clock-offset, the server and client times MUST be within
 * ~68 years (or 2^31 seconds) of each other. In the special case when the server and client
 * times are exactly 2^31 seconds apart, the library ASSUMES that the server time is ahead
 * of the client time, and returns the positive clock-offset value of INT32_MAX seconds.
 *
 * @note This API will rotate the server of use in the library for the next time request
 * (through the @ref Sntp_SendTimeRequest) if either of following events occur:
 *  - The server has responded with a rejection for the time request.
 *                         OR
 *  - The server response wait has timed out.
 * If all the servers configured in the context have been used, the API will rotate server for
 * time query back to the first server in the list which will be used in next time request.
 *
 * @param[in] pContext The context representing an SNTPv4 client.
 * @param[in] blockTimeMs The maximum duration of time (in milliseconds) the function will
 * block on receiving a response from the server unless either the response is received
 * OR a response timeout occurs.
 *
 * @note This function can be called multiple times with zero or small blocking times
 * to poll whether server response is received until either the response response is
 * received from the server OR a response timeout has occurred.
 *
 * @return This API functions returns one of the following:
 *  - #SntpSuccess if a successful server response is received.
 *  - #SntpErrorContextNotInitialized if an uninitialized or invalid context is passed
 * to the function.
 *  - #SntpErrorBadParameter if an invalid context is passed to the function.
 *  - #SntpErrorNetworkFailure if there is a failure in the user-defined transport
 *  - #SntpErrorAuthFailure if an internal error occurs in the user-defined
 * authentication interface when validating the server response.
 *  - #SntpServerNotAuthenticated when the server could not be authenticated from
 * its response with the user-defined authentication interface.
 *  - #SntpInvalidResponse if the server response fails sanity checks expected in an
 * SNTP response packet.
 *  - #SntpErrorResponseTimeout if a timeout has occurred in receiving response from
 * the server.
 *  - #SntpRejectedResponse if the server responded with a rejection for the time
 * request.
 */
/* @[define_sntp_receivetimeresponse] */
SntpStatus_t Sntp_ReceiveTimeResponse( SntpContext_t * pContext,
                                       uint32_t blockTimeMs );
/* @[define_sntp_receivetimeresponse] */

/**
 * @brief Converts @ref SntpStatus_t to its equivalent
 * string.
 *
 * @note The returned string MUST NOT be modified.
 *
 * @param[in] status The status to convert to a string.
 *
 * @return The string representation of the status
 * code.
 */
/* @[define_sntp_statustostr] */
const char * Sntp_StatusToStr( SntpStatus_t status );
/* @[define_sntp_statustostr] */

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef CORE_SNTP_CLIENT_H_ */

// === source/include/core_sntp_config_defaults.h (verbatim from upstream) ===
/*
 * coreSNTP
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_sntp_config_defaults.h
 * @brief This file represents the default values for the configuration macros
 * of the coreSNTP library.
 *
 * @note This file SHOULD NOT be modified. If custom values are needed for
 * any configuration macro, a core_sntp_config.h file should be provided to
 * the SNTP library to override the default values defined in this file.
 * To build the library with the core_sntp_config.h file, make sure to
 * not set the SNTP_DO_NOT_USE_CUSTOM_CONFIG preprocessor macro.
 */

#ifndef CORE_SNTP_CONFIG_DEFAULTS_H_
#define CORE_SNTP_CONFIG_DEFAULTS_H_

/* The macro definition for SNTP_DO_NOT_USE_CUSTOM_CONFIG is for Doxygen
 * documentation only. */

/**
 * @brief Define this macro to build the SNTP library without the custom config
 * file core_sntp_config.h.
 *
 * Without the custom config, the SNTP library builds with
 * default values of config macros defined in core_sntp_config_defaults.h file.
 *
 * If a custom config is provided, then SNTP_DO_NOT_USE_CUSTOM_CONFIG should not
 * be defined.
 */
#ifdef DOXYGEN
    #define SNTP_DO_NOT_USE_CUSTOM_CONFIG
#endif

/* SNTP_DO_NOT_USE_CUSTOM_CONFIG allows building the SNTP library
 * without a custom config. If a custom config is provided, the
 * SNTP_DO_NOT_USE_CUSTOM_CONFIG macro should not be defined. */
#ifndef SNTP_DO_NOT_USE_CUSTOM_CONFIG

#endif

/**
 * @brief Macro that is called in the SNTP library for logging "Error" level
 * messages.
 *
 * To enable error level logging in the SNTP library, this macro should be mapped to the
 * application-specific logging implementation that supports error logging.
 *
 * @note This logging macro is called in the SNTP library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_sntp_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C).
 *
 * <b>Default value</b>: Error logging is turned off, and no code is generated for calls
 * to the macro in the SNTP library on compilation.
 */
#ifndef LogError
    #define LogError( message )
#endif

/**
 * @brief Macro that is called in the SNTP library for logging "Warning" level
 * messages.
 *
 * To enable warning level logging in the SNTP library, this macro should be mapped to the
 * application-specific logging implementation that supports warning logging.
 *
 * @note This logging macro is called in the SNTP library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_sntp_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/).
 *
 * <b>Default value</b>: Warning logs are turned off, and no code is generated for calls
 * to the macro in the SNTP library on compilation.
 */
#ifndef LogWarn
    #define LogWarn( message )
#endif

/**
 * @brief Macro that is called in the SNTP library for logging "Info" level
 * messages.
 *
 * To enable info level logging in the SNTP library, this macro should be mapped to the
 * application-specific logging implementation that supports info logging.
 *
 * @note This logging macro is called in the SNTP library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_sntp_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/).
 *
 * <b>Default value</b>: Info logging is turned off, and no code is generated for calls
 * to the macro in the SNTP library on compilation.
 */
#ifndef LogInfo
    #define LogInfo( message )
#endif

/**
 * @brief Macro that is called in the SNTP library for logging "Debug" level
 * messages.
 *
 * To enable debug level logging from SNTP library, this macro should be mapped to the
 * application-specific logging implementation that supports debug logging.
 *
 * @note This logging macro is called in the SNTP library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_sntp_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/).
 *
 * <b>Default value</b>: Debug logging is turned off, and no code is generated for calls
 * to the macro in the SNTP library on compilation.
 */
#ifndef LogDebug
    #define LogDebug( message )
#endif

#endif /* ifndef CORE_SNTP_CONFIG_DEFAULTS_H_ */

// === source/core_sntp_serializer.c (verbatim from upstream) ===
/*
 * coreSNTP
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_sntp_serializer.c
 * @brief Implementation of the Serializer API of the coreSNTP library.
 */

/* Standard includes. */
#include <string.h>
#include <stdbool.h>
#include <assert.h>

/* Include API header. */

/**
 * @brief The version of SNTP supported by the coreSNTP library by complying
 * with the SNTPv4 specification defined in [RFC 4330](https://tools.ietf.org/html/rfc4330).
 */
#define SNTP_VERSION                        ( 4U )

/**
 * @brief The bit mask for the "Mode" information in the first byte of an SNTP packet.
 * The "Mode" field occupies bits 0-2 of the byte.
 * @note Refer to the [RFC 4330 Section 4](https://tools.ietf.org/html/rfc4330#section-4)
 * for more information.
 */
#define SNTP_MODE_BITS_MASK                 ( 0x07U )

/**
 * @brief The value indicating a "client" in the "Mode" field of an SNTP packet.
 * @note Refer to the [RFC 4330 Section 4](https://tools.ietf.org/html/rfc4330#section-4)
 * for more information.
 */
#define SNTP_MODE_CLIENT                    ( 3U )

/**
 * @brief The value indicating a "server" in the "Mode" field of an SNTP packet.
 * @note Refer to the [RFC 4330 Section 4](https://tools.ietf.org/html/rfc4330#section-4)
 * for more information.
 */
#define SNTP_MODE_SERVER                    ( 4U )

/**
 * @brief The position of the least significant bit of the "Leap Indicator" field
 * in first byte of an SNTP packet. The "Leap Indicator" field occupies bits 6-7 of the byte.
 * @note Refer to the [RFC 4330 Section 4](https://tools.ietf.org/html/rfc4330#section-4)
 * for more information.
 */
#define SNTP_LEAP_INDICATOR_LSB_POSITION    ( 6 )

/**
 * @brief Value of Stratum field in SNTP packet representing a Kiss-o'-Death message
 * from server.
 */
#define SNTP_KISS_OF_DEATH_STRATUM          ( 0U )

/**
 * @brief The position of least significant bit of the "Version" information
 * in the first byte of an SNTP packet. "Version" field occupies bits 3-5 of
 * the byte.
 * @note Refer to the [RFC 4330 Section 4](https://tools.ietf.org/html/rfc4330#section-4)
 * for more information.
 */
#define SNTP_VERSION_LSB_POSITION           ( 3 )

/**
 * @brief The integer value of the Kiss-o'-Death ASCII code, "DENY", used
 * for comparison with data in an SNTP response.
 * @note Refer to [RFC 4330 Section 8](https://tools.ietf.org/html/rfc4330#section-8)
 * for more information.
 */
#define KOD_CODE_DENY_UINT_VALUE            ( 0x44454e59U )

/**
 * @brief The integer value of the Kiss-o'-Death ASCII code, "RSTR", used
 * for comparison with data in an SNTP response.
 * @note Refer to [RFC 4330 Section 8](https://tools.ietf.org/html/rfc4330#section-8)
 * for more information.
 */
#define KOD_CODE_RSTR_UINT_VALUE            ( 0x52535452U )

/**
 * @brief The integer value of the Kiss-o'-Death ASCII code, "RATE", used
 * for comparison with data in an SNTP response.
 * @note Refer to [RFC 4330 Section 8](https://tools.ietf.org/html/rfc4330#section-8)
 * for more information.
 */
#define KOD_CODE_RATE_UINT_VALUE            ( 0x52415445U )

/**
 * @brief Macro to represent exactly half of the total number of seconds in an NTP era.
 * As 32 bits are used to represent the "seconds" part of an SNTP timestamp, the half of
 * the total range of seconds in an NTP era is 2^31 seconds, which represents ~68 years.
 *
 * @note This macro represents the edge case of calculating the client system clock-offset
 * relative to server time as the library ASSUMES that the client and server times are within
 * 2^31 seconds apart in duration. This is done to support calculating clock-offset for the
 * cases when server and client systems are in adjacent NTP eras, which can occur when NTP time
 * wraps around in 2036, and the relative NTP era presence of client and server times is
 * determined based on comparing first order difference values between all possible NTP era
 * configurations of the systems.
 */
#define CLOCK_OFFSET_MAX_TIME_DIFFERENCE    ( ( ( ( int64_t ) INT32_MAX + 1 ) * 1000 ) )

/**
 * @brief Macro to represent the total number of milliseconds that are represented in an
 * NTP era period. This macro represents a duration of ~136 years.
 *
 * @note Rationale for calculation: The "seconds" part of an NTP timestamp is represented in
 * unsigned 32 bit width, thus, the total range of seconds it represents is 2^32,
 * i.e. (UINT32_MAX + 1).
 */
#define TOTAL_MILLISECONDS_IN_NTP_ERA       ( ( ( int64_t ) UINT32_MAX + 1 ) * 1000 )

/**
 * @brief Structure representing an SNTP packet header.
 * For more information on SNTP packet format, refer to
 * [RFC 4330 Section 4](https://tools.ietf.org/html/rfc4330#section-4).
 *
 * @note This does not include extension fields for authentication data
 * for secure SNTP communication. Authentication data follows the
 * packet header represented by this structure.
 */
typedef struct SntpPacket
{
    /**
     * @brief Bits 6-7 leap indicator, bits 3-5 are version number, bits 0-2 are mode
     */
    uint8_t leapVersionMode;

    /**
     * @brief stratum
     */
    uint8_t stratum;

    /**
     * @brief poll interval
     */
    uint8_t poll;

    /**
     * @brief precision
     */
    uint8_t precision;

    /**
     * @brief root delay
     */
    uint32_t rootDelay;

    /**
     * @brief root dispersion
     */
    uint32_t rootDispersion;

    /**
     * @brief reference ID
     */
    uint32_t refId;

    /**
     * @brief reference time
     */
    SntpTimestamp_t refTime;

    /**
     * @brief origin timestamp
     */
    SntpTimestamp_t originTime;

    /**
     * @brief receive timestamp
     */
    SntpTimestamp_t receiveTime;

    /**
     * @brief transmit timestamp
     */
    SntpTimestamp_t transmitTime;
} SntpPacket_t;

/**
 * @brief Utility macro to fill 32-bit integer in word-sized
 * memory in network byte (or Big Endian) order.
 *
 * @param[out] pWordMemory Pointer to the word-sized memory in which
 * the 32-bit integer will be filled.
 * @param[in] data The 32-bit integer to fill in the @p wordMemory
 * in network byte order.
 *
 * @note This utility ensures that data is filled in memory
 * in expected network byte order, as an assignment operation
 * (like *pWordMemory = word) can cause undesired side-effect
 * of network-byte ordering getting reversed on Little Endian platforms.
 */
static void fillWordMemoryInNetworkOrder( uint32_t * pWordMemory,
                                          uint32_t data )
{
    uint8_t * pByteMemory = ( uint8_t * ) pWordMemory;

    assert( pWordMemory != NULL );

    pByteMemory[ 0 ] = ( uint8_t ) ( data >> 24 );
    pByteMemory[ 1 ] = ( uint8_t ) ( ( data >> 16 ) & 0x000000FFU );
    pByteMemory[ 2 ] = ( uint8_t ) ( ( data >> 8 ) & 0x000000FFU );
    pByteMemory[ 3 ] = ( uint8_t ) ( ( data ) & 0x000000FFU );
}

/**
 * @brief Utility macro to generate a 32-bit integer from memory containing
 * integer in network (or Big Endian) byte order.
 * @param[in] ptr Pointer to the memory containing 32-bit integer in network
 * byte order.
 *
 * @return The host representation of the 32-bit integer in the passed word
 * memory.
 */
static uint32_t readWordFromNetworkByteOrderMemory( const uint32_t * ptr )
{
    const uint8_t * pMemStartByte = ( const uint8_t * ) ptr;

    assert( ptr != NULL );

    return ( uint32_t ) ( ( ( ( uint32_t ) pMemStartByte[ 0 ] ) << 24 ) |
                          ( 0x00FF0000U & ( ( ( uint32_t ) pMemStartByte[ 1 ] ) << 16 ) ) |
                          ( 0x0000FF00U & ( ( ( uint32_t ) pMemStartByte[ 2 ] ) << 8 ) ) |
                          ( ( uint32_t ) pMemStartByte[ 3 ] ) );
}

/**
 * @brief Utility to return absolute (or positively signed) value of an signed
 * 64 bit integer.
 *
 * @param[in] value The integer to return the absolute value of.
 *
 * @return The absolute value of @p value.
 */
static int64_t absoluteOf( int64_t value )
{
    return ( value >= 0 ) ? value : ( ( int64_t ) 0 - value );
}

/**
 * @brief Utility to determine whether a timestamp represents a zero
 * timestamp value.
 *
 * @note This utility is used to determine whether a timestamp value is
 * invalid. According to the SNTPv4 specification, a zero timestamp value
 * is considered invalid.
 *
 * @param[in] pTime The timestamp whose value is to be inspected for
 * zero value.
 *
 * @return `true` if the timestamp is zero; otherwise `false`.
 */
static bool isZeroTimestamp( const SntpTimestamp_t * pTime )
{
    bool isSecondsZero = ( pTime->seconds == 0U ) ? true : false;
    bool isFractionsZero = ( pTime->fractions == 0U ) ? true : false;

    return( isSecondsZero && isFractionsZero );
}

/**
 * @brief Utility to convert the "fractions" part of an SNTP timestamp to milliseconds
 * duration of time.
 * @param[in] fractions The fractions value.
 *
 * @return The milliseconds equivalent of the @p fractions value.
 */
static uint32_t fractionsToMs( uint32_t fractions )
{
    return( fractions / ( 1000U * SNTP_FRACTION_VALUE_PER_MICROSECOND ) );
}

/**
 * @brief Utility to safely calculate difference between server and client timestamps and
 * return the difference in the resolution of milliseconds as a signed 64 bit integer.
 * The calculated value represents the effective subtraction as ( @p serverTimeSec - @p clientTimeSec ).
 *
 * @note This utility SUPPORTS the cases of server and client timestamps being in different NTP eras,
 * and ASSUMES that the server and client systems are within 68 years of each other.
 * To handle the case of different NTP eras, this function calculates difference values for all
 * possible combinations of NTP eras of server and client times (i.e. 1. both timestamps in same era,
 * 2. server timestamp one era ahead, and 3. client timestamp being one era ahead), and determines
 * the NTP era configuration by choosing the difference value of the smallest absolute value.
 *
 * @param[in] pServerTime The server timestamp.
 * @param[in] pClientTime The client timestamp.
 *
 * @return The calculated difference between server and client times as a signed 64 bit integer.
 */
static int64_t safeTimeDifference( const SntpTimestamp_t * pServerTime,
                                   const SntpTimestamp_t * pClientTime )
{
    int64_t eraAdjustedDiff = 0;

    /* Convert the timestamps into 64 bit signed integer values of milliseconds. */
    int64_t serverTime = ( ( int64_t ) pServerTime->seconds * 1000 ) + ( int64_t ) fractionsToMs( pServerTime->fractions );
    int64_t clientTime = ( ( int64_t ) pClientTime->seconds * 1000 ) + ( int64_t ) fractionsToMs( pClientTime->fractions );

    /* The difference between the 2 timestamps is calculated by determining the whether the timestamps
     * are present in the same NTP era or adjacent NTP eras (i.e. the NTP timestamp overflow case). */

    /* First, calculate the first order time difference assuming that server and client times
     * are in the same NTP era. */
    int64_t diffWithNoEraAdjustment = serverTime - clientTime;

    /* Store the absolute value of the time difference which will be used for comparison with
     * different cases of relative NTP era configuration of client and server times. */
    int64_t absSameEraDiff = absoluteOf( diffWithNoEraAdjustment );

    /* If the absolute difference value is 2^31 seconds, it means that the server and client times are
     * away by exactly half the range of SNTP timestamp "second" values representable in unsigned 32 bits.
     * In such a case, irrespective of whether the 2 systems exist in the same or adjacent NTP eras, the
     * time difference calculated between the systems will ALWAYS yield the same value when viewed from
     * all NTP era configurations of the times.
     * For such a case, we will ASSUME that the server time is AHEAD of client time, and thus, generate
     * a positive clock-offset value.
     */
    if( absSameEraDiff == CLOCK_OFFSET_MAX_TIME_DIFFERENCE )
    {
        /* It does not matter whether server and client are in the same era for this
         * special case as the difference value for both same and adjacent eras will yield
         * the same absolute value of 2^31.*/
        eraAdjustedDiff = CLOCK_OFFSET_MAX_TIME_DIFFERENCE;
    }
    else
    {
        /* Determine if server time belongs to an NTP era different than the client time, and accordingly
         * choose the 64 bit representation of the first order difference to account for the era.
         * The logic for determining the relative era presence of the timestamps is by calculating the
         * first order difference (of "Server Time - Client Time") for all the 3 different era combinations
         * (1. both timestamps in same era, 2. server time one era ahead, 3. client time one era ahead)
         * and choosing the NTP era configuration that has the smallest first order difference value.
         */
        int64_t diffWithServerEraAdjustment = serverTime + TOTAL_MILLISECONDS_IN_NTP_ERA -
                                              clientTime;                                     /* This helps determine whether server is an
                                                                                               * era ahead of client time. */
        int64_t diffWithClientEraAdjustment = serverTime -
                                              ( TOTAL_MILLISECONDS_IN_NTP_ERA + clientTime ); /* This helps determine whether server is an
                                                                                               * era behind of client time. */

        /* Store the absolute value equivalents of all the time difference configurations
         * for easier comparison to smallest value from them. */
        int64_t absServerEraAheadDiff = absoluteOf( diffWithServerEraAdjustment );
        int64_t absClientEraAheadDiff = absoluteOf( diffWithClientEraAdjustment );

        /* Determine the correct relative era of client and server times by checking which era
         * configuration of difference value represents the least difference. */
        if( ( absSameEraDiff <= absServerEraAheadDiff ) && ( absSameEraDiff <= absClientEraAheadDiff ) )
        {
            /* Both server and client times are in the same era. */
            eraAdjustedDiff = diffWithNoEraAdjustment;
        }
        /* Check if server time is an NTP era ahead of client time. */
        else if( absServerEraAheadDiff < absSameEraDiff )
        {
            /* Server time is in NTP era 1 while client time is in NTP era 0. */
            eraAdjustedDiff = diffWithServerEraAdjustment;
        }
        /* Now, we know that the client time is an era ahead of server time. */
        else
        {
            /* Server time is in NTP era 0 while client time is in NTP era 1. */
            eraAdjustedDiff = diffWithClientEraAdjustment;
        }
    }

    return eraAdjustedDiff;
}

/**
 * @brief Utility to calculate clock offset of system relative to the
 * server using the on-wire protocol specified in the NTPv4 specification.
 * For more information on on-wire protocol, refer to
 * [RFC 5905 Section 8](https://tools.ietf.org/html/rfc5905#section-8).
 *
 * @note The following diagram explains the calculation of the clock
 * offset:
 *
 *                 T2      T3
 *      ---------------------------------   <-----   *SNTP/NTP server*
 *               /\         \
 *               /           \
 *     Request* /             \ *Response*
 *             /              \/
 *      ---------------------------------   <-----   *SNTP client*
 *           T1                T4
 *
 *  The four most recent timestamps, T1 through T4, are used to compute
 *  the clock offset of SNTP client relative to the server where:
 *
 *     T1 = Client Request Transmit Time
 *     T2 = Server Receive Time (of client request)
 *     T3 = Server Response Transmit Time
 *     T4 = Client Receive Time (of server response)
 *
 *  Clock Offset = T(NTP/SNTP server) - T(SNTP client)
 *               = [( T2 - T1 ) + ( T3 - T4 )]
 *                 ---------------------------
 *                              2
 *
 * @note Both NTPv4 and SNTPv4 specifications suggest calculating the
 * clock offset value, if possible. As the timestamp format uses 64 bit
 * integer and there exist 2 orders of arithmetic calculations on the
 * timestamp values (subtraction followed by addition as shown in the
 * diagram above), the clock offset for the system can be calculated
 * ONLY if the value can be represented in 62 significant bits and 2 sign
 * bits i.e. if the system clock is within 34 years (in the future or past)
 * of the server time.
 *
 * @param[in] pClientTxTime The system time of sending the SNTP request.
 * This is the same as "T1" in the above diagram.
 * @param[in] pServerRxTime The server time of receiving the SNTP request
 * packet from the client. This is the same as "T2" in the above diagram.
 * @param[in] pServerTxTime The server time of sending the SNTP response
 * packet. This is the same as "T3" in the above diagram.
 * @param[in] pClientRxTime The system time of receiving the SNTP response
 * from the server. This is the same as "T4" in the above diagram.
 * @param[out] pClockOffset This will be filled with the calculated offset value
 * of the system clock relative to the server time with the assumption that the
 * system clock is within 68 years of server time.
 */
static void calculateClockOffset( const SntpTimestamp_t * pClientTxTime,
                                  const SntpTimestamp_t * pServerRxTime,
                                  const SntpTimestamp_t * pServerTxTime,
                                  const SntpTimestamp_t * pClientRxTime,
                                  int64_t * pClockOffset )
{
    /* Variable for storing the first-order difference between timestamps. */
    int64_t firstOrderDiffSend = 0;
    int64_t firstOrderDiffRecv = 0;

    assert( pClientTxTime != NULL );
    assert( pServerRxTime != NULL );
    assert( pServerTxTime != NULL );
    assert( pClientRxTime != NULL );
    assert( pClockOffset != NULL );

    /* Perform first order difference of timestamps on the network send path i.e. T2 - T1.
     * Note: The calculated difference value will always represent years in the range of
     *[-68 years, +68 years]. */
    firstOrderDiffSend = safeTimeDifference( pServerRxTime, pClientTxTime );

    /* Perform first order difference of timestamps on the network receive path i.e. T3 - T4.
     * Note: The calculated difference value will always represent years in the range of
     *[-68 years, +68 years]. */
    firstOrderDiffRecv = safeTimeDifference( pServerTxTime, pClientRxTime );

    /* Now calculate the system clock-offset relative to server time as the average of the
     * first order difference of timestamps in both directions of network path.
     * Note: This will ALWAYS represent offset in the range of [-68 years, +68 years]. */
    *pClockOffset = ( firstOrderDiffSend + firstOrderDiffRecv ) / 2;
}

/**
 * @brief Parse a SNTP response packet by determining whether it is a rejected
 * or accepted response to an SNTP request, and accordingly, populate the
 * @p pParsedResponse parameter with the parsed data.
 *
 * @note If the server has rejected the request with the a Kiss-o'-Death message,
 * then this function will set the associated rejection code in the output parameter
 * while setting the remaining members to zero.
 * If the server has accepted the time request, then the function will set the
 * rejectedResponseCode member of the output parameter to #SNTP_KISS_OF_DEATH_CODE_NONE,
 * and set the other the members with appropriate data extracted from the response
 * packet.
 *
 * @param[in] pResponsePacket The SNTP response packet from server to parse.
 * @param[in] pRequestTxTime The system time (in SNTP timestamp format) of
 * sending the SNTP request to server.
 * @param[in] pResponseRxTime The system time (in SNTP timestamp format) of
 * receiving the SNTP response from server.
 * @param[out] pParsedResponse The parameter that will be populated with data
 * parsed from the response packet, @p pResponsePacket.
 *
 * @return This function returns one of the following:
 * - #SntpSuccess if the server response does not represent a Kiss-o'-Death
 * message.
 * - #SntpRejectedResponseChangeServer if the server rejected with a code
 * indicating that client cannot be retry requests to it.
 * - #SntpRejectedResponseRetryWithBackoff if the server rejected with a code
 * indicating that client should back-off before retrying request.
 * - #SntpRejectedResponseOtherCode if the server rejected with a code
 * other than "DENY", "RSTR" and "RATE".
 */
static SntpStatus_t parseValidSntpResponse( const SntpPacket_t * pResponsePacket,
                                            const SntpTimestamp_t * pRequestTxTime,
                                            const SntpTimestamp_t * pResponseRxTime,
                                            SntpResponseData_t * pParsedResponse )
{
    SntpStatus_t status = SntpSuccess;

    assert( pResponsePacket != NULL );
    assert( pResponseRxTime != NULL );
    assert( pParsedResponse != NULL );

    /* Clear the output parameter memory to zero. */
    ( void ) memset( pParsedResponse, 0, sizeof( *pParsedResponse ) );

    /* Determine if the server has accepted or rejected the request for time. */
    if( pResponsePacket->stratum == SNTP_KISS_OF_DEATH_STRATUM )
    {
        /* Server has sent a Kiss-o'-Death message i.e. rejected the request. */

        /* Extract the kiss-code sent by the server from the "Reference ID" field
         * of the SNTP packet. */
        pParsedResponse->rejectedResponseCode =
            readWordFromNetworkByteOrderMemory( &pResponsePacket->refId );

        /* Determine the return code based on the Kiss-o'-Death code. */
        switch( pParsedResponse->rejectedResponseCode )
        {
            case KOD_CODE_DENY_UINT_VALUE:
            case KOD_CODE_RSTR_UINT_VALUE:
                status = SntpRejectedResponseChangeServer;
                break;

            case KOD_CODE_RATE_UINT_VALUE:
                status = SntpRejectedResponseRetryWithBackoff;
                break;

            default:
                status = SntpRejectedResponseOtherCode;
                break;
        }
    }
    else
    {
        /* Server has responded successfully to the time request. */

        SntpTimestamp_t serverRxTime;

        /* Map of integer value to SntpLeapSecondInfo_t enumeration type for the
         * "Leap Indicator" field in the first byte of an SNTP packet.
         * Note: This map is used to not violate MISRA Rule 10.5 when directly
         * converting an integer to enumeration type.
         */
        const SntpLeapSecondInfo_t leapIndicatorTypeMap[] =
        {
            NoLeapSecond,
            LastMinuteHas61Seconds,
            LastMinuteHas59Seconds,
            AlarmServerNotSynchronized
        };

        /* Set the Kiss-o'-Death code value to NULL as server has responded favorably
         * to the time request. */
        pParsedResponse->rejectedResponseCode = SNTP_KISS_OF_DEATH_CODE_NONE;

        /* Fill the output parameter with the server time which is the
         * "transmit" time in the response packet. */
        pParsedResponse->serverTime.seconds =
            readWordFromNetworkByteOrderMemory( &pResponsePacket->transmitTime.seconds );
        pParsedResponse->serverTime.fractions =
            readWordFromNetworkByteOrderMemory( &pResponsePacket->transmitTime.fractions );

        /* Extract information of any upcoming leap second from the response. */
        pParsedResponse->leapSecondType = leapIndicatorTypeMap[
            ( pResponsePacket->leapVersionMode >> SNTP_LEAP_INDICATOR_LSB_POSITION ) ];

        /* Store the "receive" time in SNTP response packet in host order. */
        serverRxTime.seconds =
            readWordFromNetworkByteOrderMemory( &pResponsePacket->receiveTime.seconds );
        serverRxTime.fractions =
            readWordFromNetworkByteOrderMemory( &pResponsePacket->receiveTime.fractions );

        /* Calculate system clock offset relative to server time, if possible, within
         * the 64 bit integer width of the SNTP timestamp. */
        calculateClockOffset( pRequestTxTime,
                              &serverRxTime,
                              &pParsedResponse->serverTime,
                              pResponseRxTime,
                              &pParsedResponse->clockOffsetMs );
    }

    return status;
}


SntpStatus_t Sntp_SerializeRequest( SntpTimestamp_t * pRequestTime,
                                    uint32_t randomNumber,
                                    void * pBuffer,
                                    size_t bufferSize )
{
    SntpStatus_t status = SntpSuccess;

    if( pRequestTime == NULL )
    {
        status = SntpErrorBadParameter;
    }
    else if( pBuffer == NULL )
    {
        status = SntpErrorBadParameter;
    }
    else if( bufferSize < SNTP_PACKET_BASE_SIZE )
    {
        status = SntpErrorBufferTooSmall;
    }

    /* Zero timestamps for client request time is not allowed to protect against
     * attack spoofing server response containing zero value for "originate timestamp".
     * Note: In SNTP/NTP communication, the "originate timestamp" of a valid server response
     * matches the "transmit timestamp" in corresponding client request packet. */
    else if( isZeroTimestamp( pRequestTime ) == true )
    {
        status = SntpErrorBadParameter;
    }
    else
    {
        /* MISRA Ref 11.5.1 [Void pointer assignment] */
        /* More details at: https://github.com/FreeRTOS/coreSNTP/blob/main/MISRA.md#rule-115 */
        /* coverity[misra_c_2012_rule_11_5_violation] */
        SntpPacket_t * pRequestPacket = ( SntpPacket_t * ) pBuffer;

        /* Fill the buffer with zero as most fields are zero for a standard SNTP
         * request packet.*/
        ( void ) memset( pBuffer, 0, sizeof( SntpPacket_t ) );

        /* Set the first byte of the request packet for "Version" and "Mode" fields */
        pRequestPacket->leapVersionMode = 0U /* Leap Indicator */ |
                                          ( SNTP_VERSION << SNTP_VERSION_LSB_POSITION ) /* Version Number */ |
                                          SNTP_MODE_CLIENT /* Mode */;


        /* Add passed random number to non-significant bits of the fractions part
         * of the transmit timestamp.
         * This is suggested by the SNTPv4 (and NTPv4) specification(s)
         * to protect against replay attacks. Refer to RFC 4330 Section 3 for
         * more information.
         * Adding random bits to the least significant 16 bits of the fractions
         * part of the timestamp affects only ~15 microseconds of information
         * (calculated as 0xFFFF * 232 picoseconds).
         */
        pRequestTime->fractions = ( pRequestTime->fractions
                                    | ( randomNumber >> 16 ) );

        /* Update the request buffer with request timestamp in network byte order. */
        fillWordMemoryInNetworkOrder( &pRequestPacket->transmitTime.seconds,
                                      pRequestTime->seconds );
        fillWordMemoryInNetworkOrder( &pRequestPacket->transmitTime.fractions,
                                      pRequestTime->fractions );
    }

    return status;
}


SntpStatus_t Sntp_DeserializeResponse( const SntpTimestamp_t * pRequestTime,
                                       const SntpTimestamp_t * pResponseRxTime,
                                       const void * pResponseBuffer,
                                       size_t bufferSize,
                                       SntpResponseData_t * pParsedResponse )
{
    SntpStatus_t status = SntpSuccess;
    /* MISRA Ref 11.5.1 [Void pointer assignment] */
    /* More details at: https://github.com/FreeRTOS/coreSNTP/blob/main/MISRA.md#rule-115 */
    /* coverity[misra_c_2012_rule_11_5_violation] */
    const SntpPacket_t * pResponsePacket = ( const SntpPacket_t * ) pResponseBuffer;

    if( ( pRequestTime == NULL ) || ( pResponseRxTime == NULL ) ||
        ( pResponseBuffer == NULL ) || ( pParsedResponse == NULL ) )
    {
        status = SntpErrorBadParameter;
    }
    else if( bufferSize < SNTP_PACKET_BASE_SIZE )
    {
        status = SntpErrorBufferTooSmall;
    }

    /* Zero timestamps for client request time is not allowed to protect against
     * attack spoofing server response containing zero value for "originate timestamp".
     * Note: In SNTP/NTP communication, the "originate timestamp" of a valid server response
     * matches the "transmit timestamp" in corresponding client request packet. */
    else if( isZeroTimestamp( pRequestTime ) == true )
    {
        status = SntpErrorBadParameter;
    }
    /* Check if the packet represents a server in the "Mode" field. */
    else if( ( pResponsePacket->leapVersionMode & SNTP_MODE_BITS_MASK ) != SNTP_MODE_SERVER )
    {
        status = SntpInvalidResponse;
    }

    /* Check if any of the timestamps in the response packet are zero, which is invalid.
     * Note: This is done to protect against a nuanced server spoofing attack where if the
     * SNTP client resets its internal state of "Client transmit timestamp" (OR "originate
     * timestamp" from server perspective) to zero as a protection against replay attack, an
     * an attacker with this knowledge of the client operation can spoof a server response
     * containing the "originate timestamp" as zero. Thus, to protect against such attack,
     * a server response packet with any zero timestamp is rejected. */
    else if( ( isZeroTimestamp( &pResponsePacket->originTime ) == true ) ||
             ( isZeroTimestamp( &pResponsePacket->receiveTime ) == true ) ||
             ( isZeroTimestamp( &pResponsePacket->transmitTime ) == true ) )
    {
        status = SntpInvalidResponse;
    }


    /* Validate that the server has sent the client's request timestamp in the
     * "originate" timestamp field of the response. */
    else if( ( pRequestTime->seconds !=
               readWordFromNetworkByteOrderMemory( &pResponsePacket->originTime.seconds ) ) ||
             ( pRequestTime->fractions !=
               readWordFromNetworkByteOrderMemory( &pResponsePacket->originTime.fractions ) ) )

    {
        status = SntpInvalidResponse;
    }
    else
    {
        /* As the response packet is valid, parse more information from it and
         * populate the output parameter. */

        status = parseValidSntpResponse( pResponsePacket,
                                         pRequestTime,
                                         pResponseRxTime,
                                         pParsedResponse );
    }

    return status;
}

SntpStatus_t Sntp_CalculatePollInterval( uint16_t clockFreqTolerance,
                                         uint16_t desiredAccuracy,
                                         uint32_t * pPollInterval )
{
    SntpStatus_t status = SntpSuccess;

    if( ( clockFreqTolerance == 0U ) || ( desiredAccuracy == 0U ) || ( pPollInterval == NULL ) )
    {
        status = SntpErrorBadParameter;
    }
    else
    {
        uint32_t exactIntervalForAccuracy = 0U;
        uint8_t log2PollInterval = 0U;

        /* Calculate the poll interval required for achieving the exact desired clock accuracy
         * with the following formulae:
         *
         * System Clock Drift Rate ( microseconds / second ) = Clock Frequency Tolerance (in PPM )
         * Maximum Clock Drift ( milliseconds ) = Desired Accuracy ( milliseconds )
         *
         * Poll Interval ( seconds ) =     Maximum Clock Drift
         *                              ---------------------------
         *                                System Clock Drift Rate
         *
         *                           =  Maximum Drift ( milliseconds ) * 1000 ( microseconds / millisecond )
         *                             ------------------------------------------------------------------------
         *                                        System Clock Drift Rate ( microseconds / second )
         *
         *                           =    Desired Accuracy * 1000
         *                             ------------------------------
         *                               Clock Frequency Tolerance
         */
        exactIntervalForAccuracy = ( ( uint32_t ) desiredAccuracy * 1000U ) / clockFreqTolerance;

        /* Check if calculated poll interval value falls in the supported range of seconds. */
        if( exactIntervalForAccuracy == 0U )
        {
            /* Poll interval value is less than 1 second, and is not supported by the function. */
            status = SntpZeroPollInterval;
        }
        else
        {
            /* To calculate the log 2 value of the exact poll interval value, first determine the highest
             * bit set in the value. */
            while( exactIntervalForAccuracy != 0U )
            {
                log2PollInterval++;
                exactIntervalForAccuracy /= 2U;
            }

            /* Convert the highest bit in the exact poll interval value to the nearest integer
             * value lower or equal to the log2 of the exact poll interval value. */
            log2PollInterval--;

            /* Calculate the poll interval as the closest exponent of 2 value that achieves
             * equal or higher accuracy than the desired accuracy. */
            *pPollInterval = ( ( ( uint32_t ) 1U ) << log2PollInterval );
        }
    }

    return status;
}

SntpStatus_t Sntp_ConvertToUnixTime( const SntpTimestamp_t * pSntpTime,
                                     uint32_t * pUnixTimeSecs,
                                     uint32_t * pUnixTimeMicrosecs )
{
    SntpStatus_t status = SntpSuccess;

    if( ( pSntpTime == NULL ) || ( pUnixTimeSecs == NULL ) || ( pUnixTimeMicrosecs == NULL ) )
    {
        status = SntpErrorBadParameter;
    }

    if( status == SntpSuccess )
    {
        /* Handle case when SNTP timestamp is in SNTP era 0 time range
         * (i.e. time before 7 Feb 2036 6:28:15 UTC). */
        if( pSntpTime->seconds >= SNTP_TIME_AT_UNIX_EPOCH_SECS )
        {
            *pUnixTimeSecs = pSntpTime->seconds - SNTP_TIME_AT_UNIX_EPOCH_SECS;
        }
        else
        {
            /* Handle case when timestamp represents date in SNTP era 1
             * (i.e. time from 7 Feb 2036 6:28:16 UTC onwards). */
            *pUnixTimeSecs = UNIX_TIME_SECS_AT_SNTP_ERA_1_SMALLEST_TIME + pSntpTime->seconds;
        }

        /* Convert SNTP fractions to microseconds for UNIX time. */
        *pUnixTimeMicrosecs = pSntpTime->fractions / SNTP_FRACTION_VALUE_PER_MICROSECOND;
    }

    return status;
}

// === source/core_sntp_client.c (verbatim from upstream) ===
/*
 * coreSNTP
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_sntp_client.c
 * @brief Implementation of the client API of the coreSNTP library.
 */

/* Standard includes. */
#include <assert.h>
#include <string.h>

/* SNTP client library API include. */

/**
 * @brief Utility to convert fractions part of SNTP timestamp to milliseconds.
 *
 * @param[in] fractions The fractions value in an SNTP timestamp.
 */
#define FRACTIONS_TO_MS( fractions ) \
    ( fractions / ( SNTP_FRACTION_VALUE_PER_MICROSECOND * 1000U ) )

SntpStatus_t Sntp_Init( SntpContext_t * pContext,
                        const SntpServerInfo_t * pTimeServers,
                        size_t numOfServers,
                        uint32_t serverResponseTimeoutMs,
                        uint8_t * pNetworkBuffer,
                        size_t bufferSize,
                        SntpResolveDns_t resolveDnsFunc,
                        SntpGetTime_t getSystemTimeFunc,
                        SntpSetTime_t setSystemTimeFunc,
                        const UdpTransportInterface_t * pTransportIntf,
                        const SntpAuthenticationInterface_t * pAuthIntf )
{
    SntpStatus_t status = SntpSuccess;

    /* Validate pointer parameters are not NULL. */
    if( ( pContext == NULL ) || ( pTimeServers == NULL ) ||
        ( pNetworkBuffer == NULL ) || ( resolveDnsFunc == NULL ) ||
        ( getSystemTimeFunc == NULL ) || ( setSystemTimeFunc == NULL ) ||
        ( pTransportIntf == NULL ) )
    {
        LogError( ( "Invalid parameter: Pointer parameters (except pAuthIntf) cannot be NULL" ) );

        status = SntpErrorBadParameter;
    }
    /* Validate the length of the servers list.*/
    else if( numOfServers == 0U )
    {
        LogError( ( "Invalid parameter: Size of server list cannot be zero" ) );
        status = SntpErrorBadParameter;
    }
    /* Validate that the UDP transport interface functions are valid. */
    else if( ( pTransportIntf->recvFrom == NULL ) || ( pTransportIntf->sendTo == NULL ) )
    {
        LogError( ( "Invalid parameter: Function members of UDP transport interface cannot be NULL" ) );
        status = SntpErrorBadParameter;
    }

    /* If an authentication interface is provided, validate that its function pointer
     * members are valid. */
    else if( ( pAuthIntf != NULL ) &&
             ( ( pAuthIntf->generateClientAuth == NULL ) ||
               ( pAuthIntf->validateServerAuth == NULL ) ) )
    {
        LogError( ( "Invalid parameter: Function members of authentication interface cannot be NULL" ) );
        status = SntpErrorBadParameter;
    }
    else if( bufferSize < SNTP_PACKET_BASE_SIZE )
    {
        LogError( ( "Cannot initialize context: Passed network buffer size is less than %lu bytes: "
                    "bufferSize=%lu",
                    ( unsigned long ) SNTP_PACKET_BASE_SIZE,
                    ( unsigned long ) bufferSize ) );
        status = SntpErrorBufferTooSmall;
    }
    else
    {
        /* Reset the context memory to zero. */
        ( void ) memset( pContext, 0, sizeof( SntpContext_t ) );

        /* Set the members of the context with passed parameters. */
        pContext->pTimeServers = pTimeServers;
        pContext->numOfServers = numOfServers;

        pContext->responseTimeoutMs = serverResponseTimeoutMs;

        pContext->pNetworkBuffer = pNetworkBuffer;
        pContext->bufferSize = bufferSize;

        pContext->resolveDnsFunc = resolveDnsFunc;
        pContext->getTimeFunc = getSystemTimeFunc;
        pContext->setTimeFunc = setSystemTimeFunc;

        /* Copy contents of UDP transport interface to context. */
        ( void ) memcpy( &pContext->networkIntf, pTransportIntf, sizeof( UdpTransportInterface_t ) );

        /* If authentication interface has been passed, copy its contents to the context. */
        if( pAuthIntf != NULL )
        {
            ( void ) memcpy( &pContext->authIntf, pAuthIntf, sizeof( SntpAuthenticationInterface_t ) );
        }

        /* Initialize the packet size member to the standard minimum SNTP packet size.*/
        pContext->sntpPacketSize = SNTP_PACKET_BASE_SIZE;
    }

    return status;
}

/**
 * @brief Utility to calculate the difference in milliseconds between 2
 * SNTP timestamps.
 *
 * @param[in] pCurrentTime The more recent timestamp.
 * @param[in] pOlderTime The older timestamp.
 *
 * @note This functions supports the edge case of SNTP timestamp overflow
 * when @p pCurrentTime represents time in NTP era 1 (i.e. time since 7 Feb 2036)
 * and the @p OlderTime represents time in NTP era 0 (i.e. time since 1st Jan 1900).
 *
 * @return Returns the calculated time duration between the two timestamps.
 *
 * @note This function returns the calculated time difference as unsigned 64 bit
 * to avoid integer overflow when converting time difference between the seconds part
 * of the timestamps, which are 32 bits wide, to milliseconds.
 */
static uint64_t calculateElapsedTimeMs( const SntpTimestamp_t * pCurrentTime,
                                        const SntpTimestamp_t * pOlderTime )
{
    uint64_t timeDiffMs = 0UL;
    uint32_t timeDiffSec = 0U;

    assert( pCurrentTime != NULL );
    assert( pOlderTime != NULL );

    /* Detect if SNTP time has overflown between the 2 timestamps. */
    if( pCurrentTime->seconds < pOlderTime->seconds )
    {
        /* Handle the SNTP time overflow by calculating the actual time
         * duration from pOlderTime, that exists in NTP era 0, to pCurrentTime,
         * that exists in NTP era 1. */
        timeDiffSec = ( UINT32_MAX - pOlderTime->seconds ) + /* Time in NTP era 0. */
                      1U +                                   /* Epoch time in NTP era 1, i.e. 7 Feb 2036 6h:14m:28s. */
                      pCurrentTime->seconds;                 /* Time in NTP era 1. */

        timeDiffMs = ( uint64_t ) timeDiffSec * 1000UL;
    }
    else
    {
        timeDiffSec = ( pCurrentTime->seconds - pOlderTime->seconds );
        timeDiffMs = ( uint64_t ) timeDiffSec * 1000UL;
    }

    if( pCurrentTime->fractions > pOlderTime->fractions )
    {
        timeDiffMs += ( ( uint64_t ) pCurrentTime->fractions - ( uint64_t ) pOlderTime->fractions ) /
                      ( SNTP_FRACTION_VALUE_PER_MICROSECOND * 1000UL );
    }
    else
    {
        timeDiffMs -= ( ( uint64_t ) pOlderTime->fractions - ( uint64_t ) pCurrentTime->fractions ) /
                      ( SNTP_FRACTION_VALUE_PER_MICROSECOND * 1000UL );
    }

    return timeDiffMs;
}

/**
 * @brief Validates the content of the SNTP context passed to the APIs to
 * check whether it represents an initialized context.
 *
 * @param[in] pContext The SNTP context to validate.
 *
 * @return Returns one of the following:
 * - #SntpSuccess if the context is verified to be initialized.
 * - #SntpErrorBadParameter if the context is NULL.
 * - #SntpErrorContextNotInitialized if the context is validated to be initialized.
 */
static SntpStatus_t validateContext( const SntpContext_t * pContext )
{
    SntpStatus_t status = SntpSuccess;

    /* Check if the context parameter is invalid. */
    if( pContext == NULL )
    {
        status = SntpErrorBadParameter;
        LogError( ( "Invalid context parameter: Context is NULL" ) );
    }

    /* Validate pointer parameters are not NULL. */
    else if( ( pContext->pTimeServers == NULL ) || ( pContext->pNetworkBuffer == NULL ) ||
             ( pContext->resolveDnsFunc == NULL ) ||
             ( pContext->getTimeFunc == NULL ) || ( pContext->setTimeFunc == NULL ) )
    {
        status = SntpErrorContextNotInitialized;
    }

    /* Validate the size of the configured servers list, network buffer size and the state
     * variable for the SNTP packet size.*/
    else if( ( pContext->numOfServers == 0U ) || ( pContext->bufferSize < SNTP_PACKET_BASE_SIZE ) ||
             ( pContext->sntpPacketSize < SNTP_PACKET_BASE_SIZE ) )
    {
        status = SntpErrorContextNotInitialized;
    }
    /* Validate that the UDP transport interface functions are valid. */
    else if( ( pContext->networkIntf.recvFrom == NULL ) || ( pContext->networkIntf.sendTo == NULL ) )
    {
        status = SntpErrorContextNotInitialized;
    }

    /* If an authentication interface is provided, validate that both its function pointer
     * members are valid. */
    else if( ( ( pContext->authIntf.generateClientAuth != NULL ) && ( pContext->authIntf.validateServerAuth == NULL ) ) ||
             ( ( pContext->authIntf.generateClientAuth == NULL ) && ( pContext->authIntf.validateServerAuth != NULL ) ) )
    {
        status = SntpErrorContextNotInitialized;
    }
    else
    {
        status = SntpSuccess;
    }

    if( status == SntpErrorContextNotInitialized )
    {
        LogError( ( "Invalid context parameter: Context is not initialized with Sntp_Init" ) );
    }

    return status;
}

/**
 * @brief Sends SNTP request packet to the passed server over the network
 * using transport interface's send function.
 *
 * @note For the case of zero byte transmissions over the network, this function
 * repeatedly retries the send operation by calling the transport interface
 * until either:
 * 1. The requested number of bytes @p packetSize have been sent.
 *                    OR
 * 2. There is an error in sending data over the network.
 *
 * @note This function treats partial data transmissions as error as UDP
 * transport protocol does not support partial sends.
 *
 * @param[in] pNetworkIntf The UDP transport interface to use for
 * sending data over the network.
 * @param[in] timeServer The IPv4 address of the server to send the
 * SNTP request packet to.
 * @param[in] serverPort The port of the @p timeServer to send the
 * request to.
 * @param[in] getTimeFunc The function to query system time for
 * tracking retry time period of no data transmissions.
 * @param[in] pPacket The buffer containing the SNTP packet data
 * to send over the network.
 * @param[in] packetSize The size of data in the SNTP request packet.
 * @param[in] timeoutMs The timeout period for retry attempts of sending
 * SNTP request packet over the network.
 *
 * @return Returns #SntpSuccess on successful transmission of the entire
 * SNTP request packet over the network; #SntpErrorNetworkFailure
 * to indicate failure from transport interface; #SntpErrorSendTimeout if
 * time request could not be sent over the network within the @p timeoutMs
 * duration.
 */
static SntpStatus_t sendSntpPacket( const UdpTransportInterface_t * pNetworkIntf,
                                    uint32_t timeServer,
                                    uint16_t serverPort,
                                    SntpGetTime_t getTimeFunc,
                                    const uint8_t * pPacket,
                                    uint16_t packetSize,
                                    uint32_t timeoutMs )
{
    const uint8_t * pIndex = pPacket;
    int32_t bytesSent = 0;
    SntpTimestamp_t lastSendTime;
    bool shouldRetry = false;
    SntpStatus_t status = SntpErrorSendTimeout;

    assert( pPacket != NULL );
    assert( getTimeFunc != NULL );
    assert( pNetworkIntf != NULL );
    assert( packetSize >= SNTP_PACKET_BASE_SIZE );

    /* Record the starting time of attempting to send data. This begins the retry timeout
     * window. */
    getTimeFunc( &lastSendTime );

    /* Loop until the entire packet is sent. */
    do
    {
        /* Reset flag for retrying send operation for the iteration. If request packet cannot be
         * sent and timeout has not occurred, the flag will be set later for the next iteration. */
        shouldRetry = false;

        bytesSent = pNetworkIntf->sendTo( pNetworkIntf->pUserContext,
                                          timeServer,
                                          serverPort,
                                          pIndex,
                                          packetSize );

        if( bytesSent < 0 )
        {
            LogError( ( "Unable to send request packet: Transport send failed. "
                        "ErrorCode=%ld.",
                        ( long int ) bytesSent ) );
            status = SntpErrorNetworkFailure;
        }
        else if( bytesSent == 0 )
        {
            /* No bytes were sent over the network. Retry send if we have not timed out. */

            SntpTimestamp_t currentTime;
            uint64_t elapsedTimeMs;

            getTimeFunc( &currentTime );

            /* Calculate time elapsed since last data was sent over network. */
            elapsedTimeMs = calculateElapsedTimeMs( &currentTime, &lastSendTime );

            /* Check for timeout if we have been waiting to send any data over the network. */
            if( elapsedTimeMs >= timeoutMs )
            {
                LogError( ( "Unable to send request packet: Timed out retrying send: "
                            "SendRetryTimeout=%lums",
                            ( unsigned long ) timeoutMs ) );
                status = SntpErrorSendTimeout;
            }
            else
            {
                shouldRetry = true;
            }
        }

        /* Partial sends are not supported by UDP, which only supports sending the entire datagram as a whole.
         * Thus, if the transport send function returns status representing partial send, it will be treated as failure. */
        else if( bytesSent != ( int32_t ) packetSize )
        {
            LogError( ( "Unable to send request packet: Transport send returned unexpected bytes sent. "
                        "ReturnCode=%ld, ExpectedCode=%u",
                        ( long int ) bytesSent,
                        ( unsigned int ) packetSize ) );

            status = SntpErrorNetworkFailure;
        }
        else
        {
            /* The time request packet has been sent over the network. */
            status = SntpSuccess;
        }
    } while( shouldRetry == true );

    return status;
}

/**
 * @brief Adds client authentication data to SNTP request packet by calling the
 * authentication interface.
 *
 * @param[in] pContext The SNTP context.
 *
 * @return Returns one of the following:
 * - #SntpSuccess if the interface function successfully appends client
 * authentication data.
 * - #SntpErrorAuthFailure when the interface returns either an error OR an
 * incorrect size of the client authentication data.
 */
static SntpStatus_t addClientAuthentication( SntpContext_t * pContext )
{
    SntpStatus_t status = SntpSuccess;
    uint16_t authDataSize = 0U;

    assert( pContext != NULL );
    assert( pContext->authIntf.generateClientAuth != NULL );
    assert( pContext->currentServerIndex <= pContext->numOfServers );

    status = pContext->authIntf.generateClientAuth( pContext->authIntf.pAuthContext,
                                                    &pContext->pTimeServers[ pContext->currentServerIndex ],
                                                    pContext->pNetworkBuffer,
                                                    pContext->bufferSize,
                                                    &authDataSize );

    if( status != SntpSuccess )
    {
        LogError( ( "Unable to send time request: Client authentication function failed: "
                    "RetStatus=%s", Sntp_StatusToStr( status ) ) );
    }

    /* Sanity check that the returned authentication data size fits in the remaining space
     * of the request buffer besides the first #SNTP_PACKET_BASE_SIZE bytes. */
    else if( authDataSize > ( pContext->bufferSize - SNTP_PACKET_BASE_SIZE ) )
    {
        LogError( ( "Unable to send time request: Invalid authentication code size: "
                    "AuthCodeSize=%lu, NetworkBufferSize=%lu",
                    ( unsigned long ) authDataSize,
                    ( unsigned long ) pContext->bufferSize ) );
        status = SntpErrorAuthFailure;
    }
    else
    {
        /* With the authentication data added. calculate total SNTP request packet size. The same
         * size would be expected in the SNTP response from server. */
        pContext->sntpPacketSize = SNTP_PACKET_BASE_SIZE + authDataSize;

        LogInfo( ( "Appended client authentication code to SNTP request packet:"
                   " AuthCodeSize=%lu, TotalPacketSize=%lu",
                   ( unsigned long ) authDataSize,
                   ( unsigned long ) pContext->sntpPacketSize ) );
    }

    return status;
}

SntpStatus_t Sntp_SendTimeRequest( SntpContext_t * pContext,
                                   uint32_t randomNumber,
                                   uint32_t blockTimeMs )
{
    SntpStatus_t status = SntpSuccess;

    /* Validate the context parameter. */
    status = validateContext( pContext );

    if( status == SntpSuccess )
    {
        const SntpServerInfo_t * pServer = NULL;

        /* Set local variable for the currently indexed server to use for time
         * query. */
        pServer = &pContext->pTimeServers[ pContext->currentServerIndex ];

        LogDebug( ( "Using server %.*s for time query",
                    ( int ) pServer->serverNameLen, pServer->pServerName ) );

        /* Perform DNS resolution of the currently indexed server in the list
         * of configured servers. */
        if( pContext->resolveDnsFunc( pServer, &pContext->currentServerAddr ) == false )
        {
            LogError( ( "Unable to send time request: DNS resolution failed: Server=%.*s",
                        ( int ) pServer->serverNameLen, pServer->pServerName ) );

            status = SntpErrorDnsFailure;
        }
        else
        {
            LogDebug( ( "Server DNS resolved: Address=0x%08lx",
                        ( unsigned long ) pContext->currentServerAddr ) );
        }

        if( status == SntpSuccess )
        {
            /* Obtain current system time to generate SNTP request packet. */
            pContext->getTimeFunc( &pContext->lastRequestTime );

            LogDebug( ( "Obtained current time for SNTP request packet: Time=%lus %lums",
                        ( unsigned long ) pContext->lastRequestTime.seconds,
                        ( unsigned long ) FRACTIONS_TO_MS( pContext->lastRequestTime.fractions ) ) );

            /* Generate SNTP request packet with the current system time and
             * the passed random number. */
            status = Sntp_SerializeRequest( &pContext->lastRequestTime,
                                            randomNumber,
                                            pContext->pNetworkBuffer,
                                            pContext->bufferSize );

            /* The serialization should be successful as all parameter validation has
             * been done before. */
            assert( status == SntpSuccess );
        }

        /* If an authentication interface has been configured, call the function to append client
         * authentication data to SNTP request buffer. */
        if( ( status == SntpSuccess ) && ( pContext->authIntf.generateClientAuth != NULL ) )
        {
            status = addClientAuthentication( pContext );
        }

        if( status == SntpSuccess )
        {
            LogInfo( ( "Sending serialized SNTP request packet to the server: Addr=%lu, Port=%u",
                       ( unsigned long ) pContext->currentServerAddr,
                       pContext->pTimeServers[ pContext->currentServerIndex ].port ) );

            /* Send the request packet over the network to the time server. */
            status = sendSntpPacket( &pContext->networkIntf,
                                     pContext->currentServerAddr,
                                     pContext->pTimeServers[ pContext->currentServerIndex ].port,
                                     pContext->getTimeFunc,
                                     pContext->pNetworkBuffer,
                                     pContext->sntpPacketSize,
                                     blockTimeMs );
        }
    }

    return status;
}

/**
 * @brief Utility to update the SNTP context to rotate the server of use for subsequent
 * time request(s).
 *
 * @note If there is no next server remaining, after the current server's index, in the list of
 * configured servers, the server rotation algorithm wraps around to the first server in the list.
 * The wrap around is done so that an application using the library for a long-running SNTP client
 * functionality (like a daemon task) does not become dysfunctional after all configured time
 * servers have been used up. Time synchronization can be a critical functionality for a system
 * and the wrap around logic ensures that the SNTP client continues to function in such a case.
 *
 * @note Server rotation is performed ONLY when either of:
 * - The current server responds with a rejection for time request.
 *                         OR
 * - The current server response wait has timed out.
 */
static void rotateServerForNextTimeQuery( SntpContext_t * pContext )
{
    size_t nextServerIndex = ( pContext->currentServerIndex + 1U ) % pContext->numOfServers;

    LogInfo( ( "Rotating server for next time query: PreviousServer=%.*s, NextServer=%.*s",
               ( int ) pContext->pTimeServers[ pContext->currentServerIndex ].serverNameLen,
               pContext->pTimeServers[ pContext->currentServerIndex ].pServerName,
               ( int ) pContext->pTimeServers[ nextServerIndex ].serverNameLen,
               pContext->pTimeServers[ nextServerIndex ].pServerName ) );

    pContext->currentServerIndex = nextServerIndex;
}


/**
 * @brief This function attempts to receive the SNTP response packet from a server.
 *
 * @note This function treats reads of data sizes less than the expected server response packet,
 * as an error as UDP does not support partial reads. Such a scenario can exist either due:
 * - An error in the server sending its response with smaller packet size than the request packet OR
 * - A malicious attacker spoofing or modifying server response OR
 * - An error in the UDP transport interface implementation for read operation.
 *
 * @param[in] pTransportIntf The UDP transport interface to use for receiving data from
 * the network.
 * @param[in] timeServer The server to read the response from the network.
 * @param[in] serverPort The port of the server to read the response from.
 * @param[in, out] pBuffer This will be filled with the server response read from the
 * network.
 * @param[in] responseSize The size of server response to read from the network.
 *
 * @return It returns one of the following:
 * - #SntpSuccess if an SNTP response packet is received from the network.
 * - #SntpNoResponseReceived if a server response is not received from the network.
 * - #SntpErrorNetworkFailure if there is an internal failure in reading from the network
 * in the user-defined transport interface.
 */
static SntpStatus_t receiveSntpResponse( const UdpTransportInterface_t * pTransportIntf,
                                         uint32_t timeServer,
                                         uint16_t serverPort,
                                         uint8_t * pBuffer,
                                         uint16_t responseSize )
{
    SntpStatus_t status = SntpNoResponseReceived;
    int32_t bytesRead = 0;

    assert( pTransportIntf != NULL );
    assert( pTransportIntf->recvFrom != NULL );
    assert( pBuffer != NULL );
    assert( responseSize >= SNTP_PACKET_BASE_SIZE );

    bytesRead = pTransportIntf->recvFrom( pTransportIntf->pUserContext,
                                          timeServer,
                                          serverPort,
                                          pBuffer,
                                          responseSize );

    /* Negative return code indicates error. */
    if( bytesRead < 0 )
    {
        status = SntpErrorNetworkFailure;
        LogError( ( "Unable to receive server response: Transport receive failed: Code=%ld",
                    ( long int ) bytesRead ) );
    }
    /* If the packet was not available on the network, check whether we can retry. */
    else if( bytesRead == 0 )
    {
        status = SntpNoResponseReceived;
    }

    /* Partial reads are not supported by UDP, which only supports receiving the entire datagram as a whole.
     * Thus, if the transport receive function returns reception of partial data, it will be treated as failure. */
    else if( bytesRead != ( int32_t ) responseSize )
    {
        LogError( ( "Failed to receive server response: Transport recv returned less than expected bytes."
                    "ExpectedBytes=%u, ReadBytes=%ld",
                    responseSize,
                    ( long int ) bytesRead ) );
        status = SntpErrorNetworkFailure;
    }
    else
    {
        LogDebug( ( "Received server response: PacketSize=%ld", ( long int ) bytesRead ) );
        status = SntpSuccess;
    }

    return status;
}

/**
 * @brief Processes the response from a server by de-serializing the SNTP packet to
 * validate the server (if an authentication interface has been configured), determine
 * whether server has accepted or rejected the time request, and update the system clock
 * if the server responded positively with time.
 *
 * @param[in] pContext The SNTP context representing the SNTP client.
 * @param[in] pResponseRxTime The time of receiving the server response from the network.
 *
 * @return It returns one of the following:
 * - #SntpSuccess if the server response is successfully de-serialized and system clock
 * updated.
 * - #SntpErrorAuthFailure if there is internal failure in user-defined authentication
 * interface when validating server from the response.
 * - #SntpServerNotAuthenticated if the server failed authenticated check in the user-defined
 * interface.
 * - #SntpRejectedResponse if the server has rejected the time request in its response.
 * - #SntpInvalidResponse if the server response failed sanity checks.
 */
static SntpStatus_t processServerResponse( SntpContext_t * pContext,
                                           const SntpTimestamp_t * pResponseRxTime )
{
    SntpStatus_t status = SntpSuccess;
    const SntpServerInfo_t * pServer = &pContext->pTimeServers[ pContext->currentServerIndex ];

    assert( pContext != NULL );
    assert( pResponseRxTime != NULL );

    if( pContext->authIntf.validateServerAuth != NULL )
    {
        /* Verify the server from the authentication data in the SNTP response packet. */
        status = pContext->authIntf.validateServerAuth( pContext->authIntf.pAuthContext,
                                                        pServer,
                                                        pContext->pNetworkBuffer,
                                                        pContext->sntpPacketSize );
        assert( ( status == SntpSuccess ) || ( status == SntpErrorAuthFailure ) ||
                ( status == SntpServerNotAuthenticated ) );

        if( status != SntpSuccess )
        {
            LogError( ( "Unable to use server response: Server authentication function failed: "
                        "ReturnStatus=%s", Sntp_StatusToStr( status ) ) );
        }
        else
        {
            LogDebug( ( "Server response has been validated: Server=%.*s",
                        ( int ) pServer->serverNameLen, pServer->pServerName ) );
        }
    }

    if( status == SntpSuccess )
    {
        SntpResponseData_t parsedResponse = { 0 };

        /* De-serialize response packet to determine whether the server accepted or rejected
         * the request for time. Also, calculate the system clock offset if the server responded
         * with time. */
        status = Sntp_DeserializeResponse( &pContext->lastRequestTime,
                                           pResponseRxTime,
                                           pContext->pNetworkBuffer,
                                           pContext->sntpPacketSize,
                                           &parsedResponse );

        /* We do not expect the following errors to be returned as the context
         * has been validated in the Sntp_ReceiveTimeResponse API. */
        assert( status != SntpErrorBadParameter );
        assert( status != SntpErrorBufferTooSmall );

        if( ( status == SntpRejectedResponseChangeServer ) ||
            ( status == SntpRejectedResponseRetryWithBackoff ) ||
            ( status == SntpRejectedResponseOtherCode ) )
        {
            /* Server has rejected the time request. Thus, we will rotate to the next time server
             * in the list. */
            rotateServerForNextTimeQuery( pContext );

            LogError( ( "Unable to use server response: Server has rejected request for time: RejectionCode=%.*s",
                        ( int ) SNTP_KISS_OF_DEATH_CODE_LENGTH,
                        ( char * ) &parsedResponse.rejectedResponseCode ) );

            status = SntpRejectedResponse;
        }
        else if( status == SntpInvalidResponse )
        {
            LogError( ( "Unable to use server response: Server response failed sanity checks." ) );
        }
        else
        {
            /* Server has responded successfully with time, and we have calculated the clock offset
             * of system clock relative to the server.*/
            LogDebug( ( "Updating system time: ServerTime=%lu %lums ClockOffset=%lds",
                        ( unsigned long ) parsedResponse.serverTime.seconds,
                        ( unsigned long ) FRACTIONS_TO_MS( parsedResponse.serverTime.fractions ),
                        /* Print out in seconds instead of Ms to account for C90 lack of %lld */
                        ( long ) parsedResponse.clockOffsetMs / 1000 ) );

            /* Update the system clock with the calculated offset. */
            pContext->setTimeFunc( pServer, &parsedResponse.serverTime,
                                   parsedResponse.clockOffsetMs, parsedResponse.leapSecondType );

            status = SntpSuccess;
        }
    }

    /* Reset the last request time state in context to protect against replay attacks.
     * Note: The last request time is not cleared when a rejection response packet is received and the client does
     * has not authenticated server from the response. This is because clearing of the state causes the coreSNTP
     * library to discard any subsequent server response packets (as the "originate timestamp" of those packets will
     * not match the last request time value of the context), and thus, an attacker can cause Denial of Service
     * attacks by spoofing server response before the actual server is able to respond.
     */
    if( ( status == SntpSuccess ) ||
        ( ( pContext->authIntf.validateServerAuth != NULL ) && ( status == SntpRejectedResponse ) ) )
    {
        /* In the attack of SNTP request packet being replayed, the replayed request packet is serviced by
         * SNTP/NTP server with SNTP response (as servers are stateless) and client receives the response
         * containing new values of server timestamps but the stale value of "originate timestamp".
         * To prevent the coreSNTP library from servicing such a server response (associated with the replayed
         * SNTP request packet), the last request timestamp state is cleared in the context after receiving the
         * first valid server response. Therefore, any subsequent server response(s) from replayed client request
         * packets can be invalidated due to the "originate timestamp" not matching the last request time stored
         * in the context.
         * Note: If an attacker spoofs a server response with a zero "originate timestamp" after the coreSNTP
         * library (i.e. the SNTP client) has cleared the internal state to zero, the spoofed packet will be
         * discarded as the coreSNTP serializer does not accept server responses with zero value for timestamps.
         */
        pContext->lastRequestTime.seconds = 0U;
        pContext->lastRequestTime.fractions = 0U;
    }

    return status;
}

/**
 * @brief Determines whether a retry attempt should be made to receive server response packet from the network
 * depending on the timing constraints of server response timeout, @p responseTimeoutMs, and the block time
 * period, @p blockTimeMs, passed. If neither of the time windows have expired, the function determines that the
 * read operation can be re-tried.
 *
 * @param[in] pCurrentTime The current time in the system used for calculating elapsed time windows.
 * @param[in] pReadStartTime The time of the first read attempt in the current set of read tries occurring
 * from the Sntp_ReceiveTimeRequest API call by the application. This time is used for calculating the elapsed
 * time to determine whether the block time has expired.
 * @param[in] pRequestTime The time of sending the SNTP request to the server for which the response is
 * awaited. This time is used for calculating total elapsed elapsed time of waiting for server response to
 * determine if a server response timeout has occurred.
 * @param[in] responseTimeoutMs The server response timeout configuration.
 * @param[in] blockTimeMs The maximum block time of waiting for server response across read tries in the current
 * call made by application to Sntp_ReceiveTimeResponse API.
 * @param[out] pHasResponseTimedOut This will be populated with state to indicate whether the wait for server
 * response has timed out.
 *
 * @return Returns true for retrying read operation of server response; false on either server response timeout
 * OR completion of block time window.
 */
static bool decideAboutReadRetry( const SntpTimestamp_t * pCurrentTime,
                                  const SntpTimestamp_t * pReadStartTime,
                                  const SntpTimestamp_t * pRequestTime,
                                  uint32_t responseTimeoutMs,
                                  uint32_t blockTimeMs,
                                  bool * pHasResponseTimedOut )
{
    uint64_t timeSinceRequestMs = 0UL;
    uint64_t timeElapsedInReadAttempts = 0UL;
    bool shouldRetry = false;

    assert( pCurrentTime != NULL );
    assert( pReadStartTime != NULL );
    assert( pRequestTime != NULL );
    assert( pHasResponseTimedOut != NULL );

    /* Calculate time elapsed since the time request was sent to the server
     * to determine whether the server response has timed out. */
    timeSinceRequestMs = calculateElapsedTimeMs( pCurrentTime, pRequestTime );

    /* Calculate the time elapsed across all the read attempts so far to determine
     * whether the block time window for reading server response has expired. */
    timeElapsedInReadAttempts = calculateElapsedTimeMs( pCurrentTime, pReadStartTime );

    /* Check whether a response timeout has occurred to inform whether we should
     * wait for server response anymore. */
    if( timeSinceRequestMs >= ( uint64_t ) responseTimeoutMs )
    {
        shouldRetry = false;
        *pHasResponseTimedOut = true;

        LogError( ( "Unable to receive response: Server response has timed out: "
                    "RequestTime=%lus %lums, TimeoutDuration=%lums, ElapsedTime=%lus",
                    ( unsigned long ) pRequestTime->seconds,
                    ( unsigned long ) FRACTIONS_TO_MS( pRequestTime->fractions ),
                    ( unsigned long ) responseTimeoutMs,
                    /* Print out in seconds instead of Ms to account for C90 lack of %llu */
                    ( unsigned long ) ( ( timeSinceRequestMs + 500UL ) / 1000UL ) ) );
    }
    /* Check whether the block time window has expired to determine whether read can be retried. */
    else if( timeElapsedInReadAttempts >= ( uint64_t ) blockTimeMs )
    {
        shouldRetry = false;
        LogDebug( ( "Did not receive server response: Read block time has expired: "
                    "BlockTime=%lums, ResponseWaitElapsedTime=%lus",
                    ( unsigned long ) blockTimeMs,
                    /* Print out in seconds instead of Ms to account for C90 lack of %llu */
                    ( unsigned long ) ( ( timeSinceRequestMs + 500UL ) / 1000UL ) ) );
    }
    else
    {
        shouldRetry = true;
        LogDebug( ( "Did not receive server response: Retrying read: "
                    "BlockTime=%lums, ResponseWaitElapsedTime=%lus, ResponseTimeout=%lums",
                    ( unsigned long ) blockTimeMs,
                    /* Print out in seconds instead of Ms to account for C90 lack of %llu */
                    ( unsigned long ) ( ( timeSinceRequestMs + 500UL ) / 1000UL ),
                    ( unsigned long ) responseTimeoutMs ) );
    }

    return shouldRetry;
}

SntpStatus_t Sntp_ReceiveTimeResponse( SntpContext_t * pContext,
                                       uint32_t blockTimeMs )
{
    SntpStatus_t status = SntpNoResponseReceived;
    bool hasResponseTimedOut = false;

    /* Validate the context parameter. */
    status = validateContext( pContext );

    if( status == SntpSuccess )
    {
        SntpTimestamp_t startTime, currentTime;
        const SntpTimestamp_t * pRequestTime = &pContext->lastRequestTime;
        bool shouldRetry = false;

        /* Record time before read attempts so that it can be used as base time for
         * for tracking the block time window across read retries. */
        pContext->getTimeFunc( &startTime );

        do
        {
            /* Reset the retry read operation flag. If the server response is not received in the current iteration's read
             * attempt and the wait has not timed out, the flag will be set to perform a retry. */
            shouldRetry = false;

            /* Make an attempt to read the server response from the network. */
            status = receiveSntpResponse( &pContext->networkIntf,
                                          pContext->currentServerAddr,
                                          pContext->pTimeServers[ pContext->currentServerIndex ].port,
                                          pContext->pNetworkBuffer,
                                          pContext->sntpPacketSize );

            /* If the server response is received, deserialize it, validate the server
             * (if authentication interface is provided), and update system time with
             * the calculated clock offset. */
            if( status == SntpSuccess )
            {
                /* Get current time to de-serialize the receive server response packet. */
                pContext->getTimeFunc( &currentTime );

                status = processServerResponse( pContext, &currentTime );
            }
            else if( status == SntpNoResponseReceived )
            {
                /* Get current time to determine whether another attempt for reading the packet can
                 * be made. */
                pContext->getTimeFunc( &currentTime );

                /* Set the flag to retry read of server response from the network. */
                shouldRetry = decideAboutReadRetry( &currentTime,
                                                    &startTime,
                                                    pRequestTime,
                                                    pContext->responseTimeoutMs,
                                                    blockTimeMs,
                                                    &hasResponseTimedOut );
            }
            else
            {
                /* Empty else marker. */
            }
        } while( shouldRetry == true );

        /* If the wait for server response to the time request has timed out, rotate the server of use in the
         * context for subsequent time request(s). Also, update the return status to indicate response timeout. */
        if( hasResponseTimedOut == true )
        {
            status = SntpErrorResponseTimeout;

            /* Rotate server to the next in the list of configured servers in the context. */
            rotateServerForNextTimeQuery( pContext );
        }
    }

    return status;
}

const char * Sntp_StatusToStr( SntpStatus_t status )
{
    const char * pString = NULL;

    switch( status )
    {
        case SntpSuccess:
            pString = "SntpSuccess";
            break;

        case SntpErrorBadParameter:
            pString = "SntpErrorBadParameter";
            break;

        case SntpRejectedResponse:
            pString = "SntpRejectedResponse";
            break;

        case SntpRejectedResponseChangeServer:
            pString = "SntpRejectedResponseChangeServer";
            break;

        case SntpRejectedResponseRetryWithBackoff:
            pString = "SntpRejectedResponseRetryWithBackoff";
            break;

        case SntpRejectedResponseOtherCode:
            pString = "SntpRejectedResponseOtherCode";
            break;

        case SntpErrorBufferTooSmall:
            pString = "SntpErrorBufferTooSmall";
            break;

        case SntpInvalidResponse:
            pString = "SntpInvalidResponse";
            break;

        case SntpZeroPollInterval:
            pString = "SntpZeroPollInterval";
            break;

        case SntpErrorDnsFailure:
            pString = "SntpErrorDnsFailure";
            break;

        case SntpErrorNetworkFailure:
            pString = "SntpErrorNetworkFailure";
            break;

        case SntpServerNotAuthenticated:
            pString = "SntpServerNotAuthenticated";
            break;

        case SntpErrorAuthFailure:
            pString = "SntpErrorAuthFailure";
            break;

        case SntpErrorSendTimeout:
            pString = "SntpErrorSendTimeout";
            break;

        case SntpErrorResponseTimeout:
            pString = "SntpErrorResponseTimeout";
            break;

        case SntpNoResponseReceived:
            pString = "SntpNoResponseReceived";
            break;

        case SntpErrorContextNotInitialized:
            pString = "SntpErrorContextNotInitialized";
            break;

        default:
            pString = "Invalid status code!";
            break;
    }

    return pString;
}

// === test/cbmc/include/core_sntp_config.h (CBMC include, verbatim from upstream) ===
/*
 * coreSNTP
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_sntp_config_defaults.h
 * @brief This file represents the default values for the configuration macros
 * of the coreSNTP library.
 *
 * @note This file SHOULD NOT be modified. If custom values are needed for
 * any configuration macro, a core_sntp_config.h file should be provided to
 * the SNTP library to override the default values defined in this file.
 * To build the library with the core_sntp_config.h file, make sure to
 * not set the SNTP_DO_NOT_USE_CUSTOM_CONFIG preprocessor macro.
 */

#ifndef CORE_SNTP_CONFIG_DEFAULTS_H_
#define CORE_SNTP_CONFIG_DEFAULTS_H_

/* The macro definition for SNTP_DO_NOT_USE_CUSTOM_CONFIG is for Doxygen
 * documentation only. */

/**
 * @brief Define this macro to build the SNTP library without the custom config
 * file core_sntp_config.h.
 *
 * Without the custom config, the SNTP library builds with
 * default values of config macros defined in core_sntp_config_defaults.h file.
 *
 * If a custom config is provided, then SNTP_DO_NOT_USE_CUSTOM_CONFIG should not
 * be defined.
 */
#ifdef DOXYGEN
    #define SNTP_DO_NOT_USE_CUSTOM_CONFIG
#endif

/**
 * @brief The maximum duration between non-empty network reads while
 * receiving an SNTP packet via the #Sntp_ReceiveTimeResponse API function.
 *
 * When an incoming SNTP packet is detected, the transport receive function
 * may be called multiple times until all of the expected number of bytes of the
 * packet are received. This timeout represents the maximum polling duration that
 * is allowed without any data reception from the network for the incoming packet.
 *
 * If the timeout expires, the #Sntp_ReceiveTimeResponse function will return
 * #SntpErrorNetworkFailure.
 *
 * <b>Possible values:</b> Any positive 16 bit integer. Recommended to use a
 * small timeout value. <br>
 * <b>Default value:</b> `10`
 */
#ifndef SNTP_RECV_POLLING_TIMEOUT_MS
    #define SNTP_RECV_POLLING_TIMEOUT_MS    ( 10U )
#endif

/**
 * @brief The maximum duration between non-empty network transmissions while
 * sending an SNTP packet via the #Sntp_SendTimeRequest API function.
 *
 * When sending an SNTP packet, the transport send function may be called multiple
 * times until all of the required number of bytes are sent.
 * This timeout represents the maximum duration that is allowed for no data
 * transmission over the network through the transport send function.
 *
 * If the timeout expires, the #Sntp_SendTimeRequest function will return
 * #SntpErrorNetworkFailure.
 *
 * <b>Possible values:</b> Any positive 16 bit integer. Recommended to use a small
 * timeout value. <br>
 * <b>Default value:</b> `10`
 */
#ifndef SNTP_SEND_RETRY_TIMEOUT_MS
    #define SNTP_SEND_RETRY_TIMEOUT_MS    ( 10U )
#endif

/**
 * @brief Macro that is called in the SNTP library for logging "Error" level
 * messages.
 *
 * To enable error level logging in the SNTP library, this macro should be mapped to the
 * application-specific logging implementation that supports error logging.
 *
 * @note This logging macro is called in the SNTP library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_sntp_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C).
 *
 * <b>Default value</b>: Error logging is turned off, and no code is generated for calls
 * to the macro in the SNTP library on compilation.
 */
#ifndef LogError
    #define LogError( message )
#endif

/**
 * @brief Macro that is called in the SNTP library for logging "Warning" level
 * messages.
 *
 * To enable warning level logging in the SNTP library, this macro should be mapped to the
 * application-specific logging implementation that supports warning logging.
 *
 * @note This logging macro is called in the SNTP library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_sntp_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/).
 *
 * <b>Default value</b>: Warning logs are turned off, and no code is generated for calls
 * to the macro in the SNTP library on compilation.
 */
#ifndef LogWarn
    #define LogWarn( message )
#endif

/**
 * @brief Macro that is called in the SNTP library for logging "Info" level
 * messages.
 *
 * To enable info level logging in the SNTP library, this macro should be mapped to the
 * application-specific logging implementation that supports info logging.
 *
 * @note This logging macro is called in the SNTP library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_sntp_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/).
 *
 * <b>Default value</b>: Info logging is turned off, and no code is generated for calls
 * to the macro in the SNTP library on compilation.
 */
#ifndef LogInfo
    #define LogInfo( message )
#endif

/**
 * @brief Macro that is called in the SNTP library for logging "Debug" level
 * messages.
 *
 * To enable debug level logging from SNTP library, this macro should be mapped to the
 * application-specific logging implementation that supports debug logging.
 *
 * @note This logging macro is called in the SNTP library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_sntp_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/).
 *
 * <b>Default value</b>: Debug logging is turned off, and no code is generated for calls
 * to the macro in the SNTP library on compilation.
 */
#ifndef LogDebug
    #define LogDebug( message )
#endif

#endif /* ifndef CORE_SNTP_CONFIG_DEFAULTS_H_ */

// === test/cbmc/include/core_sntp_stubs.h (CBMC include, verbatim from upstream) ===
/*
 * coreSNTP
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_sntp_stubs_stubs.h
 * @brief Stubs definitions of UDP transport interface and authentication interface of coreSNTP API.
 */
#ifndef CORE_SNTP_CBMC_STUBS_H_
#define CORE_SNTP_CBMC_STUBS_H_

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

/**
 * @brief Application defined network interface send function.
 *
 * @param[in] pNetworkContext Application defined network interface context.
 * @param[in] serverAddr Server address to which application sends data.
 * @param[in] serverPort Server port to which application sends data.
 * @param[out] pBuffer SNTP network send buffer.
 * @param[in] bytesToSend Number of bytes to send over the network.
 *
 * @return Any value from INT32_MIN to INT32_MAX.
 */
int32_t NetworkInterfaceSendStub( NetworkContext_t * pNetworkContext,
                                  uint32_t serverAddr,
                                  uint16_t serverPort,
                                  const void * pBuffer,
                                  uint16_t bytesToSend );

/**
 * @brief Application defined network interface receive function.
 *
 * @param[in] pNetworkContext Application defined network interface context.
 * @param[in] serverAddr Server address from which application receives data.
 * @param[in] serverPort Server port from which application receives data.
 * @param[out] pBuffer SNTP network receive buffer.
 * @param[in] bytesToRecv SNTP requested bytes.
 *
 * @return Any value from INT32_MIN to INT32_MAX.
 */
int32_t NetworkInterfaceReceiveStub( NetworkContext_t * pNetworkContext,
                                     uint32_t serverAddr,
                                     uint16_t serverPort,
                                     void * pBuffer,
                                     uint16_t bytesToRecv );

/**
 * @brief Application defined function to generate and append
 * authentication code in an SNTP request buffer for the SNTP client to be
 * authenticated by the time server, if a security mechanism is used.
 *
 * @param[in] pContext Application defined authentication interface context.
 * @param[in] pTimeServer The time server being used to request time from.
 * This parameter is useful to choose the security mechanism when multiple time
 * servers are configured in the library, and they require different security
 * mechanisms or authentication credentials to use.
 * @param[in] pBuffer SNTP request buffer.
 * @param[in] bufferSize The maximum amount of data that can be held by the buffer.
 * @param[out] pAuthCodeSize This should be filled with size of the authentication
 * data appended to the SNTP request buffer, @p pBuffer.
 *
 * @return The function SHOULD return one of the following integer codes:
 * - #SntpSuccess when the authentication data is successfully appended to @p pBuffer.
 * - #SntpErrorBufferTooSmall when the user-supplied buffer (to the SntpContext_t through
 * @ref Sntp_Init) is not large enough to hold authentication data.
 */
SntpStatus_t GenerateClientAuthStub( SntpAuthContext_t * pContext,
                                     const SntpServerInfo_t * pTimeServer,
                                     void * pBuffer,
                                     size_t bufferSize,
                                     uint16_t * pAuthCodeSize );

/**
 * @brief Application defined function to authenticate server by validating
 * the authentication code present in its SNTP response to a time request, if
 * a security mechanism is supported by the server.
 *
 * @param[in,out] pContext The application defined NetworkContext_t which
 * is opaque to the coreSNTP library.
 * @param[in] pTimeServer The time server that has to be authenticated from its
 * SNTP response.
 * @param[in] pResponseData The SNTP response from the server that contains the
 * authentication code after the first #SNTP_PACKET_BASE_SIZE bytes.
 * @param[in] responseSize The total size of the response from the server.
 *
 * @return The function ALWAYS returns #SntpSuccess
 */
SntpStatus_t ValidateServerAuthStub( SntpAuthContext_t * pContext,
                                     const SntpServerInfo_t * pTimeServer,
                                     const void * pResponseData,
                                     uint16_t responseSize );

/**
 * @brief Application defined function to resolve time server domain-name
 * to an IPv4 address.
 *
 * @param[in] pTimeServer The time-server whose IPv4 address is to be resolved.
 * @param[out] pIpV4Addr This should be filled with the resolved IPv4 address.
 * of @p pTimeServer.
 *
 * @return `true` if DNS resolution is successful; otherwise `false` to represent
 * failure.
 */
bool ResolveDnsFuncStub( const SntpServerInfo_t * pServerAddr,
                         uint32_t * pIpV4Addr );

/**
 * @brief Application defined function to obtain the current system time
 * in SNTP timestamp format.
 *
 * @param[out] pCurrentTime This should be filled with the current system time
 * in SNTP timestamp format.
 */
void GetTimeFuncStub( SntpTimestamp_t * pCurrentTime );

/**
 * @brief Application defined function to update the system clock time
 * so that it is synchronized the time server used for getting current time.
 *
 * @param[in] pTimeServer The time server used to request time.
 * @param[in] pServerTime The current time returned by the @p pTimeServer.
 * @param[in] clockOffSetMs The calculated clock offset of the system relative
 * to the server time.
 * @param[in] leapSecondInfo Information about whether there is about an upcoming
 * leap second adjustment.
 */
void SetTimeFuncStub( const SntpServerInfo_t * pTimeServer,
                      const SntpTimestamp_t * pServerTime,
                      int64_t clockOffsetMs,
                      SntpLeapSecondInfo_t leapSecondInfo );

#endif /* ifndef CORE_SNTP_CBMC_STUBS_H_ */

// === test/cbmc/include/core_sntp_cbmc_state.h (CBMC include, verbatim from upstream) ===
/*
 * coreSNTP
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_sntp_cbmc_state.h
 * @brief Allocation and assumption utilities for the SNTP library CBMC proofs.
 */
#ifndef CORE_SNTP_CBMC_STATE_H_
#define CORE_SNTP_CBMC_STATE_H_

/* Application defined Network context. */
struct NetworkContext
{
    void * networkContext;
};

/* Application defined authentication context. */
struct SntpAuthContext
{
    void * authContext;
};

/**
 * @brief Allocate a #SntpContext_t object.
 *
 * @return NULL or allocated #SntpContext_t memory.
 */
SntpContext_t * unconstrainedCoreSntpContext();

#endif /* ifndef CORE_SNTP_CBMC_STATE_H_ */


// === Harness body, folded into main() ===
/*
 * coreSNTP
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file Sntp_SerializeRequest_harness.c
 * @brief Implements the proof harness for Sntp_SerializeRequest function.
 */


int main(void) {
    SntpTimestamp_t * pRequestTime;
    uint32_t randomNumber;
    void * pBuffer;
    size_t bufferSize;
    SntpStatus_t sntpStatus;

    pRequestTime = malloc( sizeof( SntpTimestamp_t ) );

    __CPROVER_assume( bufferSize < CBMC_MAX_OBJECT_SIZE );

    pBuffer = malloc( bufferSize );

    sntpStatus = Sntp_SerializeRequest( pRequestTime, randomNumber, pBuffer, bufferSize );

    __CPROVER_assert( ( sntpStatus == SntpErrorBadParameter || sntpStatus == SntpErrorBufferTooSmall || sntpStatus == SntpSuccess ), "The return value is not a valid SNTP Status" );
    return 0;
}
