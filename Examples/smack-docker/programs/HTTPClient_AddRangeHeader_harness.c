// Imported verbatim from FreeRTOS/coreHTTP
//   test/cbmc/proofs/HTTPClient_AddRangeHeader/HTTPClient_AddRangeHeader_harness.c
// Source bundle: llhttp.h, test/cbmc/include/core_http_config.h, source/interface/transport_interface.h, source/include/core_http_client.h, source/include/core_http_client_private.h, source/include/core_http_config_defaults.h, source/core_http_client.c
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

// === llhttp.h (verbatim from upstream) ===

#ifndef INCLUDE_LLHTTP_H_
#define INCLUDE_LLHTTP_H_

#define LLHTTP_VERSION_MAJOR 9
#define LLHTTP_VERSION_MINOR 4
#define LLHTTP_VERSION_PATCH 1

#ifndef INCLUDE_LLHTTP_ITSELF_H_
#define INCLUDE_LLHTTP_ITSELF_H_
#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>

typedef struct llhttp__internal_s llhttp__internal_t;
struct llhttp__internal_s {
  int32_t _index;
  void* _span_pos0;
  void* _span_cb0;
  int32_t error;
  const char* reason;
  const char* error_pos;
  void* data;
  void* _current;
  uint64_t content_length;
  uint8_t type;
  uint8_t method;
  uint8_t http_major;
  uint8_t http_minor;
  uint8_t header_state;
  uint16_t lenient_flags;
  uint8_t upgrade;
  uint8_t finish;
  uint16_t flags;
  uint16_t status_code;
  uint8_t initial_message_completed;
  void* settings;
};

int llhttp__internal_init(llhttp__internal_t* s);
int llhttp__internal_execute(llhttp__internal_t* s, const char* p, const char* endp);

#ifdef __cplusplus
}  /* extern "C" */
#endif
#endif  /* INCLUDE_LLHTTP_ITSELF_H_ */


#ifndef LLLLHTTP_C_HEADERS_
#define LLLLHTTP_C_HEADERS_
#ifdef __cplusplus
extern "C" {
#endif

enum llhttp_errno {
  HPE_OK = 0,
  HPE_INTERNAL = 1,
  HPE_STRICT = 2,
  HPE_LF_EXPECTED = 3,
  HPE_UNEXPECTED_CONTENT_LENGTH = 4,
  HPE_CLOSED_CONNECTION = 5,
  HPE_INVALID_METHOD = 6,
  HPE_INVALID_URL = 7,
  HPE_INVALID_CONSTANT = 8,
  HPE_INVALID_VERSION = 9,
  HPE_INVALID_HEADER_TOKEN = 10,
  HPE_INVALID_CONTENT_LENGTH = 11,
  HPE_INVALID_CHUNK_SIZE = 12,
  HPE_INVALID_STATUS = 13,
  HPE_INVALID_EOF_STATE = 14,
  HPE_INVALID_TRANSFER_ENCODING = 15,
  HPE_CB_MESSAGE_BEGIN = 16,
  HPE_CB_HEADERS_COMPLETE = 17,
  HPE_CB_MESSAGE_COMPLETE = 18,
  HPE_CB_CHUNK_HEADER = 19,
  HPE_CB_CHUNK_COMPLETE = 20,
  HPE_PAUSED = 21,
  HPE_PAUSED_UPGRADE = 22,
  HPE_PAUSED_H2_UPGRADE = 23,
  HPE_USER = 24,
  HPE_CR_EXPECTED = 25,
  HPE_CB_URL_COMPLETE = 26,
  HPE_CB_STATUS_COMPLETE = 27,
  HPE_CB_HEADER_FIELD_COMPLETE = 28,
  HPE_CB_HEADER_VALUE_COMPLETE = 29,
  HPE_UNEXPECTED_SPACE = 30,
  HPE_CB_RESET = 31,
  HPE_CB_METHOD_COMPLETE = 32,
  HPE_CB_VERSION_COMPLETE = 33,
  HPE_CB_CHUNK_EXTENSION_NAME_COMPLETE = 34,
  HPE_CB_CHUNK_EXTENSION_VALUE_COMPLETE = 35,
  HPE_CB_PROTOCOL_COMPLETE = 38
};
typedef enum llhttp_errno llhttp_errno_t;

enum llhttp_flags {
  F_CONNECTION_KEEP_ALIVE = 0x1,
  F_CONNECTION_CLOSE = 0x2,
  F_CONNECTION_UPGRADE = 0x4,
  F_CHUNKED = 0x8,
  F_UPGRADE = 0x10,
  F_CONTENT_LENGTH = 0x20,
  F_SKIPBODY = 0x40,
  F_TRAILING = 0x80,
  F_TRANSFER_ENCODING = 0x200
};
typedef enum llhttp_flags llhttp_flags_t;

enum llhttp_lenient_flags {
  LENIENT_HEADERS = 0x1,
  LENIENT_CHUNKED_LENGTH = 0x2,
  LENIENT_KEEP_ALIVE = 0x4,
  LENIENT_TRANSFER_ENCODING = 0x8,
  LENIENT_VERSION = 0x10,
  LENIENT_DATA_AFTER_CLOSE = 0x20,
  LENIENT_OPTIONAL_LF_AFTER_CR = 0x40,
  LENIENT_OPTIONAL_CRLF_AFTER_CHUNK = 0x80,
  LENIENT_OPTIONAL_CR_BEFORE_LF = 0x100,
  LENIENT_SPACES_AFTER_CHUNK_SIZE = 0x200,
  LENIENT_HEADER_VALUE_RELAXED = 0x400
};
typedef enum llhttp_lenient_flags llhttp_lenient_flags_t;

enum llhttp_type {
  HTTP_BOTH = 0,
  HTTP_REQUEST = 1,
  HTTP_RESPONSE = 2
};
typedef enum llhttp_type llhttp_type_t;

enum llhttp_finish {
  HTTP_FINISH_SAFE = 0,
  HTTP_FINISH_SAFE_WITH_CB = 1,
  HTTP_FINISH_UNSAFE = 2
};
typedef enum llhttp_finish llhttp_finish_t;

enum llhttp_method {
  HTTP_DELETE = 0,
  HTTP_GET = 1,
  HTTP_HEAD = 2,
  HTTP_POST = 3,
  HTTP_PUT = 4,
  HTTP_CONNECT = 5,
  HTTP_OPTIONS = 6,
  HTTP_TRACE = 7,
  HTTP_COPY = 8,
  HTTP_LOCK = 9,
  HTTP_MKCOL = 10,
  HTTP_MOVE = 11,
  HTTP_PROPFIND = 12,
  HTTP_PROPPATCH = 13,
  HTTP_SEARCH = 14,
  HTTP_UNLOCK = 15,
  HTTP_BIND = 16,
  HTTP_REBIND = 17,
  HTTP_UNBIND = 18,
  HTTP_ACL = 19,
  HTTP_REPORT = 20,
  HTTP_MKACTIVITY = 21,
  HTTP_CHECKOUT = 22,
  HTTP_MERGE = 23,
  HTTP_MSEARCH = 24,
  HTTP_NOTIFY = 25,
  HTTP_SUBSCRIBE = 26,
  HTTP_UNSUBSCRIBE = 27,
  HTTP_PATCH = 28,
  HTTP_PURGE = 29,
  HTTP_MKCALENDAR = 30,
  HTTP_LINK = 31,
  HTTP_UNLINK = 32,
  HTTP_SOURCE = 33,
  HTTP_PRI = 34,
  HTTP_DESCRIBE = 35,
  HTTP_ANNOUNCE = 36,
  HTTP_SETUP = 37,
  HTTP_PLAY = 38,
  HTTP_PAUSE = 39,
  HTTP_TEARDOWN = 40,
  HTTP_GET_PARAMETER = 41,
  HTTP_SET_PARAMETER = 42,
  HTTP_REDIRECT = 43,
  HTTP_RECORD = 44,
  HTTP_FLUSH = 45,
  HTTP_QUERY = 46
};
typedef enum llhttp_method llhttp_method_t;

enum llhttp_status {
  HTTP_STATUS_CONTINUE = 100,
  HTTP_STATUS_SWITCHING_PROTOCOLS = 101,
  HTTP_STATUS_PROCESSING = 102,
  HTTP_STATUS_EARLY_HINTS = 103,
  HTTP_STATUS_RESPONSE_IS_STALE = 110,
  HTTP_STATUS_REVALIDATION_FAILED = 111,
  HTTP_STATUS_DISCONNECTED_OPERATION = 112,
  HTTP_STATUS_HEURISTIC_EXPIRATION = 113,
  HTTP_STATUS_MISCELLANEOUS_WARNING = 199,
  HTTP_STATUS_OK = 200,
  HTTP_STATUS_CREATED = 201,
  HTTP_STATUS_ACCEPTED = 202,
  HTTP_STATUS_NON_AUTHORITATIVE_INFORMATION = 203,
  HTTP_STATUS_NO_CONTENT = 204,
  HTTP_STATUS_RESET_CONTENT = 205,
  HTTP_STATUS_PARTIAL_CONTENT = 206,
  HTTP_STATUS_MULTI_STATUS = 207,
  HTTP_STATUS_ALREADY_REPORTED = 208,
  HTTP_STATUS_TRANSFORMATION_APPLIED = 214,
  HTTP_STATUS_IM_USED = 226,
  HTTP_STATUS_MISCELLANEOUS_PERSISTENT_WARNING = 299,
  HTTP_STATUS_MULTIPLE_CHOICES = 300,
  HTTP_STATUS_MOVED_PERMANENTLY = 301,
  HTTP_STATUS_FOUND = 302,
  HTTP_STATUS_SEE_OTHER = 303,
  HTTP_STATUS_NOT_MODIFIED = 304,
  HTTP_STATUS_USE_PROXY = 305,
  HTTP_STATUS_SWITCH_PROXY = 306,
  HTTP_STATUS_TEMPORARY_REDIRECT = 307,
  HTTP_STATUS_PERMANENT_REDIRECT = 308,
  HTTP_STATUS_BAD_REQUEST = 400,
  HTTP_STATUS_UNAUTHORIZED = 401,
  HTTP_STATUS_PAYMENT_REQUIRED = 402,
  HTTP_STATUS_FORBIDDEN = 403,
  HTTP_STATUS_NOT_FOUND = 404,
  HTTP_STATUS_METHOD_NOT_ALLOWED = 405,
  HTTP_STATUS_NOT_ACCEPTABLE = 406,
  HTTP_STATUS_PROXY_AUTHENTICATION_REQUIRED = 407,
  HTTP_STATUS_REQUEST_TIMEOUT = 408,
  HTTP_STATUS_CONFLICT = 409,
  HTTP_STATUS_GONE = 410,
  HTTP_STATUS_LENGTH_REQUIRED = 411,
  HTTP_STATUS_PRECONDITION_FAILED = 412,
  HTTP_STATUS_PAYLOAD_TOO_LARGE = 413,
  HTTP_STATUS_URI_TOO_LONG = 414,
  HTTP_STATUS_UNSUPPORTED_MEDIA_TYPE = 415,
  HTTP_STATUS_RANGE_NOT_SATISFIABLE = 416,
  HTTP_STATUS_EXPECTATION_FAILED = 417,
  HTTP_STATUS_IM_A_TEAPOT = 418,
  HTTP_STATUS_PAGE_EXPIRED = 419,
  HTTP_STATUS_ENHANCE_YOUR_CALM = 420,
  HTTP_STATUS_MISDIRECTED_REQUEST = 421,
  HTTP_STATUS_UNPROCESSABLE_ENTITY = 422,
  HTTP_STATUS_LOCKED = 423,
  HTTP_STATUS_FAILED_DEPENDENCY = 424,
  HTTP_STATUS_TOO_EARLY = 425,
  HTTP_STATUS_UPGRADE_REQUIRED = 426,
  HTTP_STATUS_PRECONDITION_REQUIRED = 428,
  HTTP_STATUS_TOO_MANY_REQUESTS = 429,
  HTTP_STATUS_REQUEST_HEADER_FIELDS_TOO_LARGE_UNOFFICIAL = 430,
  HTTP_STATUS_REQUEST_HEADER_FIELDS_TOO_LARGE = 431,
  HTTP_STATUS_LOGIN_TIMEOUT = 440,
  HTTP_STATUS_NO_RESPONSE = 444,
  HTTP_STATUS_RETRY_WITH = 449,
  HTTP_STATUS_BLOCKED_BY_PARENTAL_CONTROL = 450,
  HTTP_STATUS_UNAVAILABLE_FOR_LEGAL_REASONS = 451,
  HTTP_STATUS_CLIENT_CLOSED_LOAD_BALANCED_REQUEST = 460,
  HTTP_STATUS_INVALID_X_FORWARDED_FOR = 463,
  HTTP_STATUS_REQUEST_HEADER_TOO_LARGE = 494,
  HTTP_STATUS_SSL_CERTIFICATE_ERROR = 495,
  HTTP_STATUS_SSL_CERTIFICATE_REQUIRED = 496,
  HTTP_STATUS_HTTP_REQUEST_SENT_TO_HTTPS_PORT = 497,
  HTTP_STATUS_INVALID_TOKEN = 498,
  HTTP_STATUS_CLIENT_CLOSED_REQUEST = 499,
  HTTP_STATUS_INTERNAL_SERVER_ERROR = 500,
  HTTP_STATUS_NOT_IMPLEMENTED = 501,
  HTTP_STATUS_BAD_GATEWAY = 502,
  HTTP_STATUS_SERVICE_UNAVAILABLE = 503,
  HTTP_STATUS_GATEWAY_TIMEOUT = 504,
  HTTP_STATUS_HTTP_VERSION_NOT_SUPPORTED = 505,
  HTTP_STATUS_VARIANT_ALSO_NEGOTIATES = 506,
  HTTP_STATUS_INSUFFICIENT_STORAGE = 507,
  HTTP_STATUS_LOOP_DETECTED = 508,
  HTTP_STATUS_BANDWIDTH_LIMIT_EXCEEDED = 509,
  HTTP_STATUS_NOT_EXTENDED = 510,
  HTTP_STATUS_NETWORK_AUTHENTICATION_REQUIRED = 511,
  HTTP_STATUS_WEB_SERVER_UNKNOWN_ERROR = 520,
  HTTP_STATUS_WEB_SERVER_IS_DOWN = 521,
  HTTP_STATUS_CONNECTION_TIMEOUT = 522,
  HTTP_STATUS_ORIGIN_IS_UNREACHABLE = 523,
  HTTP_STATUS_TIMEOUT_OCCURED = 524,
  HTTP_STATUS_SSL_HANDSHAKE_FAILED = 525,
  HTTP_STATUS_INVALID_SSL_CERTIFICATE = 526,
  HTTP_STATUS_RAILGUN_ERROR = 527,
  HTTP_STATUS_SITE_IS_OVERLOADED = 529,
  HTTP_STATUS_SITE_IS_FROZEN = 530,
  HTTP_STATUS_IDENTITY_PROVIDER_AUTHENTICATION_ERROR = 561,
  HTTP_STATUS_NETWORK_READ_TIMEOUT = 598,
  HTTP_STATUS_NETWORK_CONNECT_TIMEOUT = 599
};
typedef enum llhttp_status llhttp_status_t;

#define HTTP_ERRNO_MAP(XX) \
  XX(0, OK, OK) \
  XX(1, INTERNAL, INTERNAL) \
  XX(2, STRICT, STRICT) \
  XX(3, LF_EXPECTED, LF_EXPECTED) \
  XX(4, UNEXPECTED_CONTENT_LENGTH, UNEXPECTED_CONTENT_LENGTH) \
  XX(5, CLOSED_CONNECTION, CLOSED_CONNECTION) \
  XX(6, INVALID_METHOD, INVALID_METHOD) \
  XX(7, INVALID_URL, INVALID_URL) \
  XX(8, INVALID_CONSTANT, INVALID_CONSTANT) \
  XX(9, INVALID_VERSION, INVALID_VERSION) \
  XX(10, INVALID_HEADER_TOKEN, INVALID_HEADER_TOKEN) \
  XX(11, INVALID_CONTENT_LENGTH, INVALID_CONTENT_LENGTH) \
  XX(12, INVALID_CHUNK_SIZE, INVALID_CHUNK_SIZE) \
  XX(13, INVALID_STATUS, INVALID_STATUS) \
  XX(14, INVALID_EOF_STATE, INVALID_EOF_STATE) \
  XX(15, INVALID_TRANSFER_ENCODING, INVALID_TRANSFER_ENCODING) \
  XX(16, CB_MESSAGE_BEGIN, CB_MESSAGE_BEGIN) \
  XX(17, CB_HEADERS_COMPLETE, CB_HEADERS_COMPLETE) \
  XX(18, CB_MESSAGE_COMPLETE, CB_MESSAGE_COMPLETE) \
  XX(19, CB_CHUNK_HEADER, CB_CHUNK_HEADER) \
  XX(20, CB_CHUNK_COMPLETE, CB_CHUNK_COMPLETE) \
  XX(21, PAUSED, PAUSED) \
  XX(22, PAUSED_UPGRADE, PAUSED_UPGRADE) \
  XX(23, PAUSED_H2_UPGRADE, PAUSED_H2_UPGRADE) \
  XX(24, USER, USER) \
  XX(25, CR_EXPECTED, CR_EXPECTED) \
  XX(26, CB_URL_COMPLETE, CB_URL_COMPLETE) \
  XX(27, CB_STATUS_COMPLETE, CB_STATUS_COMPLETE) \
  XX(28, CB_HEADER_FIELD_COMPLETE, CB_HEADER_FIELD_COMPLETE) \
  XX(29, CB_HEADER_VALUE_COMPLETE, CB_HEADER_VALUE_COMPLETE) \
  XX(30, UNEXPECTED_SPACE, UNEXPECTED_SPACE) \
  XX(31, CB_RESET, CB_RESET) \
  XX(32, CB_METHOD_COMPLETE, CB_METHOD_COMPLETE) \
  XX(33, CB_VERSION_COMPLETE, CB_VERSION_COMPLETE) \
  XX(34, CB_CHUNK_EXTENSION_NAME_COMPLETE, CB_CHUNK_EXTENSION_NAME_COMPLETE) \
  XX(35, CB_CHUNK_EXTENSION_VALUE_COMPLETE, CB_CHUNK_EXTENSION_VALUE_COMPLETE) \
  XX(38, CB_PROTOCOL_COMPLETE, CB_PROTOCOL_COMPLETE) \


#define HTTP_METHOD_MAP(XX) \
  XX(0, DELETE, DELETE) \
  XX(1, GET, GET) \
  XX(2, HEAD, HEAD) \
  XX(3, POST, POST) \
  XX(4, PUT, PUT) \
  XX(5, CONNECT, CONNECT) \
  XX(6, OPTIONS, OPTIONS) \
  XX(7, TRACE, TRACE) \
  XX(8, COPY, COPY) \
  XX(9, LOCK, LOCK) \
  XX(10, MKCOL, MKCOL) \
  XX(11, MOVE, MOVE) \
  XX(12, PROPFIND, PROPFIND) \
  XX(13, PROPPATCH, PROPPATCH) \
  XX(14, SEARCH, SEARCH) \
  XX(15, UNLOCK, UNLOCK) \
  XX(16, BIND, BIND) \
  XX(17, REBIND, REBIND) \
  XX(18, UNBIND, UNBIND) \
  XX(19, ACL, ACL) \
  XX(20, REPORT, REPORT) \
  XX(21, MKACTIVITY, MKACTIVITY) \
  XX(22, CHECKOUT, CHECKOUT) \
  XX(23, MERGE, MERGE) \
  XX(24, MSEARCH, M-SEARCH) \
  XX(25, NOTIFY, NOTIFY) \
  XX(26, SUBSCRIBE, SUBSCRIBE) \
  XX(27, UNSUBSCRIBE, UNSUBSCRIBE) \
  XX(28, PATCH, PATCH) \
  XX(29, PURGE, PURGE) \
  XX(30, MKCALENDAR, MKCALENDAR) \
  XX(31, LINK, LINK) \
  XX(32, UNLINK, UNLINK) \
  XX(33, SOURCE, SOURCE) \
  XX(46, QUERY, QUERY) \


#define RTSP_METHOD_MAP(XX) \
  XX(1, GET, GET) \
  XX(3, POST, POST) \
  XX(6, OPTIONS, OPTIONS) \
  XX(35, DESCRIBE, DESCRIBE) \
  XX(36, ANNOUNCE, ANNOUNCE) \
  XX(37, SETUP, SETUP) \
  XX(38, PLAY, PLAY) \
  XX(39, PAUSE, PAUSE) \
  XX(40, TEARDOWN, TEARDOWN) \
  XX(41, GET_PARAMETER, GET_PARAMETER) \
  XX(42, SET_PARAMETER, SET_PARAMETER) \
  XX(43, REDIRECT, REDIRECT) \
  XX(44, RECORD, RECORD) \
  XX(45, FLUSH, FLUSH) \


#define HTTP_ALL_METHOD_MAP(XX) \
  XX(0, DELETE, DELETE) \
  XX(1, GET, GET) \
  XX(2, HEAD, HEAD) \
  XX(3, POST, POST) \
  XX(4, PUT, PUT) \
  XX(5, CONNECT, CONNECT) \
  XX(6, OPTIONS, OPTIONS) \
  XX(7, TRACE, TRACE) \
  XX(8, COPY, COPY) \
  XX(9, LOCK, LOCK) \
  XX(10, MKCOL, MKCOL) \
  XX(11, MOVE, MOVE) \
  XX(12, PROPFIND, PROPFIND) \
  XX(13, PROPPATCH, PROPPATCH) \
  XX(14, SEARCH, SEARCH) \
  XX(15, UNLOCK, UNLOCK) \
  XX(16, BIND, BIND) \
  XX(17, REBIND, REBIND) \
  XX(18, UNBIND, UNBIND) \
  XX(19, ACL, ACL) \
  XX(20, REPORT, REPORT) \
  XX(21, MKACTIVITY, MKACTIVITY) \
  XX(22, CHECKOUT, CHECKOUT) \
  XX(23, MERGE, MERGE) \
  XX(24, MSEARCH, M-SEARCH) \
  XX(25, NOTIFY, NOTIFY) \
  XX(26, SUBSCRIBE, SUBSCRIBE) \
  XX(27, UNSUBSCRIBE, UNSUBSCRIBE) \
  XX(28, PATCH, PATCH) \
  XX(29, PURGE, PURGE) \
  XX(30, MKCALENDAR, MKCALENDAR) \
  XX(31, LINK, LINK) \
  XX(32, UNLINK, UNLINK) \
  XX(33, SOURCE, SOURCE) \
  XX(34, PRI, PRI) \
  XX(35, DESCRIBE, DESCRIBE) \
  XX(36, ANNOUNCE, ANNOUNCE) \
  XX(37, SETUP, SETUP) \
  XX(38, PLAY, PLAY) \
  XX(39, PAUSE, PAUSE) \
  XX(40, TEARDOWN, TEARDOWN) \
  XX(41, GET_PARAMETER, GET_PARAMETER) \
  XX(42, SET_PARAMETER, SET_PARAMETER) \
  XX(43, REDIRECT, REDIRECT) \
  XX(44, RECORD, RECORD) \
  XX(45, FLUSH, FLUSH) \
  XX(46, QUERY, QUERY) \


#define HTTP_STATUS_MAP(XX) \
  XX(100, CONTINUE, CONTINUE) \
  XX(101, SWITCHING_PROTOCOLS, SWITCHING_PROTOCOLS) \
  XX(102, PROCESSING, PROCESSING) \
  XX(103, EARLY_HINTS, EARLY_HINTS) \
  XX(110, RESPONSE_IS_STALE, RESPONSE_IS_STALE) \
  XX(111, REVALIDATION_FAILED, REVALIDATION_FAILED) \
  XX(112, DISCONNECTED_OPERATION, DISCONNECTED_OPERATION) \
  XX(113, HEURISTIC_EXPIRATION, HEURISTIC_EXPIRATION) \
  XX(199, MISCELLANEOUS_WARNING, MISCELLANEOUS_WARNING) \
  XX(200, OK, OK) \
  XX(201, CREATED, CREATED) \
  XX(202, ACCEPTED, ACCEPTED) \
  XX(203, NON_AUTHORITATIVE_INFORMATION, NON_AUTHORITATIVE_INFORMATION) \
  XX(204, NO_CONTENT, NO_CONTENT) \
  XX(205, RESET_CONTENT, RESET_CONTENT) \
  XX(206, PARTIAL_CONTENT, PARTIAL_CONTENT) \
  XX(207, MULTI_STATUS, MULTI_STATUS) \
  XX(208, ALREADY_REPORTED, ALREADY_REPORTED) \
  XX(214, TRANSFORMATION_APPLIED, TRANSFORMATION_APPLIED) \
  XX(226, IM_USED, IM_USED) \
  XX(299, MISCELLANEOUS_PERSISTENT_WARNING, MISCELLANEOUS_PERSISTENT_WARNING) \
  XX(300, MULTIPLE_CHOICES, MULTIPLE_CHOICES) \
  XX(301, MOVED_PERMANENTLY, MOVED_PERMANENTLY) \
  XX(302, FOUND, FOUND) \
  XX(303, SEE_OTHER, SEE_OTHER) \
  XX(304, NOT_MODIFIED, NOT_MODIFIED) \
  XX(305, USE_PROXY, USE_PROXY) \
  XX(306, SWITCH_PROXY, SWITCH_PROXY) \
  XX(307, TEMPORARY_REDIRECT, TEMPORARY_REDIRECT) \
  XX(308, PERMANENT_REDIRECT, PERMANENT_REDIRECT) \
  XX(400, BAD_REQUEST, BAD_REQUEST) \
  XX(401, UNAUTHORIZED, UNAUTHORIZED) \
  XX(402, PAYMENT_REQUIRED, PAYMENT_REQUIRED) \
  XX(403, FORBIDDEN, FORBIDDEN) \
  XX(404, NOT_FOUND, NOT_FOUND) \
  XX(405, METHOD_NOT_ALLOWED, METHOD_NOT_ALLOWED) \
  XX(406, NOT_ACCEPTABLE, NOT_ACCEPTABLE) \
  XX(407, PROXY_AUTHENTICATION_REQUIRED, PROXY_AUTHENTICATION_REQUIRED) \
  XX(408, REQUEST_TIMEOUT, REQUEST_TIMEOUT) \
  XX(409, CONFLICT, CONFLICT) \
  XX(410, GONE, GONE) \
  XX(411, LENGTH_REQUIRED, LENGTH_REQUIRED) \
  XX(412, PRECONDITION_FAILED, PRECONDITION_FAILED) \
  XX(413, PAYLOAD_TOO_LARGE, PAYLOAD_TOO_LARGE) \
  XX(414, URI_TOO_LONG, URI_TOO_LONG) \
  XX(415, UNSUPPORTED_MEDIA_TYPE, UNSUPPORTED_MEDIA_TYPE) \
  XX(416, RANGE_NOT_SATISFIABLE, RANGE_NOT_SATISFIABLE) \
  XX(417, EXPECTATION_FAILED, EXPECTATION_FAILED) \
  XX(418, IM_A_TEAPOT, IM_A_TEAPOT) \
  XX(419, PAGE_EXPIRED, PAGE_EXPIRED) \
  XX(420, ENHANCE_YOUR_CALM, ENHANCE_YOUR_CALM) \
  XX(421, MISDIRECTED_REQUEST, MISDIRECTED_REQUEST) \
  XX(422, UNPROCESSABLE_ENTITY, UNPROCESSABLE_ENTITY) \
  XX(423, LOCKED, LOCKED) \
  XX(424, FAILED_DEPENDENCY, FAILED_DEPENDENCY) \
  XX(425, TOO_EARLY, TOO_EARLY) \
  XX(426, UPGRADE_REQUIRED, UPGRADE_REQUIRED) \
  XX(428, PRECONDITION_REQUIRED, PRECONDITION_REQUIRED) \
  XX(429, TOO_MANY_REQUESTS, TOO_MANY_REQUESTS) \
  XX(430, REQUEST_HEADER_FIELDS_TOO_LARGE_UNOFFICIAL, REQUEST_HEADER_FIELDS_TOO_LARGE_UNOFFICIAL) \
  XX(431, REQUEST_HEADER_FIELDS_TOO_LARGE, REQUEST_HEADER_FIELDS_TOO_LARGE) \
  XX(440, LOGIN_TIMEOUT, LOGIN_TIMEOUT) \
  XX(444, NO_RESPONSE, NO_RESPONSE) \
  XX(449, RETRY_WITH, RETRY_WITH) \
  XX(450, BLOCKED_BY_PARENTAL_CONTROL, BLOCKED_BY_PARENTAL_CONTROL) \
  XX(451, UNAVAILABLE_FOR_LEGAL_REASONS, UNAVAILABLE_FOR_LEGAL_REASONS) \
  XX(460, CLIENT_CLOSED_LOAD_BALANCED_REQUEST, CLIENT_CLOSED_LOAD_BALANCED_REQUEST) \
  XX(463, INVALID_X_FORWARDED_FOR, INVALID_X_FORWARDED_FOR) \
  XX(494, REQUEST_HEADER_TOO_LARGE, REQUEST_HEADER_TOO_LARGE) \
  XX(495, SSL_CERTIFICATE_ERROR, SSL_CERTIFICATE_ERROR) \
  XX(496, SSL_CERTIFICATE_REQUIRED, SSL_CERTIFICATE_REQUIRED) \
  XX(497, HTTP_REQUEST_SENT_TO_HTTPS_PORT, HTTP_REQUEST_SENT_TO_HTTPS_PORT) \
  XX(498, INVALID_TOKEN, INVALID_TOKEN) \
  XX(499, CLIENT_CLOSED_REQUEST, CLIENT_CLOSED_REQUEST) \
  XX(500, INTERNAL_SERVER_ERROR, INTERNAL_SERVER_ERROR) \
  XX(501, NOT_IMPLEMENTED, NOT_IMPLEMENTED) \
  XX(502, BAD_GATEWAY, BAD_GATEWAY) \
  XX(503, SERVICE_UNAVAILABLE, SERVICE_UNAVAILABLE) \
  XX(504, GATEWAY_TIMEOUT, GATEWAY_TIMEOUT) \
  XX(505, HTTP_VERSION_NOT_SUPPORTED, HTTP_VERSION_NOT_SUPPORTED) \
  XX(506, VARIANT_ALSO_NEGOTIATES, VARIANT_ALSO_NEGOTIATES) \
  XX(507, INSUFFICIENT_STORAGE, INSUFFICIENT_STORAGE) \
  XX(508, LOOP_DETECTED, LOOP_DETECTED) \
  XX(509, BANDWIDTH_LIMIT_EXCEEDED, BANDWIDTH_LIMIT_EXCEEDED) \
  XX(510, NOT_EXTENDED, NOT_EXTENDED) \
  XX(511, NETWORK_AUTHENTICATION_REQUIRED, NETWORK_AUTHENTICATION_REQUIRED) \
  XX(520, WEB_SERVER_UNKNOWN_ERROR, WEB_SERVER_UNKNOWN_ERROR) \
  XX(521, WEB_SERVER_IS_DOWN, WEB_SERVER_IS_DOWN) \
  XX(522, CONNECTION_TIMEOUT, CONNECTION_TIMEOUT) \
  XX(523, ORIGIN_IS_UNREACHABLE, ORIGIN_IS_UNREACHABLE) \
  XX(524, TIMEOUT_OCCURED, TIMEOUT_OCCURED) \
  XX(525, SSL_HANDSHAKE_FAILED, SSL_HANDSHAKE_FAILED) \
  XX(526, INVALID_SSL_CERTIFICATE, INVALID_SSL_CERTIFICATE) \
  XX(527, RAILGUN_ERROR, RAILGUN_ERROR) \
  XX(529, SITE_IS_OVERLOADED, SITE_IS_OVERLOADED) \
  XX(530, SITE_IS_FROZEN, SITE_IS_FROZEN) \
  XX(561, IDENTITY_PROVIDER_AUTHENTICATION_ERROR, IDENTITY_PROVIDER_AUTHENTICATION_ERROR) \
  XX(598, NETWORK_READ_TIMEOUT, NETWORK_READ_TIMEOUT) \
  XX(599, NETWORK_CONNECT_TIMEOUT, NETWORK_CONNECT_TIMEOUT) \


#ifdef __cplusplus
}  /* extern "C" */
#endif
#endif  /* LLLLHTTP_C_HEADERS_ */


#ifndef INCLUDE_LLHTTP_API_H_
#define INCLUDE_LLHTTP_API_H_
#ifdef __cplusplus
extern "C" {
#endif
#include <stddef.h>

#if defined(__wasm__)
#define LLHTTP_EXPORT __attribute__((visibility("default")))
#elif defined(_WIN32)
#define LLHTTP_EXPORT __declspec(dllexport)
#else
#define LLHTTP_EXPORT
#endif

typedef llhttp__internal_t llhttp_t;
typedef struct llhttp_settings_s llhttp_settings_t;

typedef int (*llhttp_data_cb)(llhttp_t*, const char *at, size_t length);
typedef int (*llhttp_cb)(llhttp_t*);

struct llhttp_settings_s {
  /* Possible return values 0, -1, `HPE_PAUSED` */
  llhttp_cb      on_message_begin;

  /* Possible return values 0, -1, HPE_USER */
  llhttp_data_cb on_protocol;
  llhttp_data_cb on_url;
  llhttp_data_cb on_status;
  llhttp_data_cb on_method;
  llhttp_data_cb on_version;
  llhttp_data_cb on_header_field;
  llhttp_data_cb on_header_value;
  llhttp_data_cb      on_chunk_extension_name;
  llhttp_data_cb      on_chunk_extension_value;

  /* Possible return values:
   * 0  - Proceed normally
   * 1  - Assume that request/response has no body, and proceed to parsing the
   *      next message
   * 2  - Assume absence of body (as above) and make `llhttp_execute()` return
   *      `HPE_PAUSED_UPGRADE`
   * -1 - Error
   * `HPE_PAUSED`
   */
  llhttp_cb      on_headers_complete;

  /* Possible return values 0, -1, HPE_USER */
  llhttp_data_cb on_body;

  /* Possible return values 0, -1, `HPE_PAUSED` */
  llhttp_cb      on_message_complete;
  llhttp_cb      on_protocol_complete;
  llhttp_cb      on_url_complete;
  llhttp_cb      on_status_complete;
  llhttp_cb      on_method_complete;
  llhttp_cb      on_version_complete;
  llhttp_cb      on_header_field_complete;
  llhttp_cb      on_header_value_complete;
  llhttp_cb      on_chunk_extension_name_complete;
  llhttp_cb      on_chunk_extension_value_complete;

  /* When on_chunk_header is called, the current chunk length is stored
   * in parser->content_length.
   * Possible return values 0, -1, `HPE_PAUSED`
   */
  llhttp_cb      on_chunk_header;
  llhttp_cb      on_chunk_complete;
  llhttp_cb      on_reset;
};

/* Initialize the parser with specific type and user settings.
 *
 * NOTE: lifetime of `settings` has to be at least the same as the lifetime of
 * the `parser` here. In practice, `settings` has to be either a static
 * variable or be allocated with `malloc`, `new`, etc.
 */
LLHTTP_EXPORT
void llhttp_init(llhttp_t* parser, llhttp_type_t type,
                 const llhttp_settings_t* settings);

LLHTTP_EXPORT
llhttp_t* llhttp_alloc(llhttp_type_t type);

LLHTTP_EXPORT
void llhttp_free(llhttp_t* parser);

LLHTTP_EXPORT
uint8_t llhttp_get_type(llhttp_t* parser);

LLHTTP_EXPORT
uint8_t llhttp_get_http_major(llhttp_t* parser);

LLHTTP_EXPORT
uint8_t llhttp_get_http_minor(llhttp_t* parser);

LLHTTP_EXPORT
uint8_t llhttp_get_method(llhttp_t* parser);

LLHTTP_EXPORT
int llhttp_get_status_code(llhttp_t* parser);

LLHTTP_EXPORT
uint8_t llhttp_get_upgrade(llhttp_t* parser);

/* Reset an already initialized parser back to the start state, preserving the
 * existing parser type, callback settings, user data, and lenient flags.
 */
LLHTTP_EXPORT
void llhttp_reset(llhttp_t* parser);

/* Initialize the settings object */
LLHTTP_EXPORT
void llhttp_settings_init(llhttp_settings_t* settings);

/* Parse full or partial request/response, invoking user callbacks along the
 * way.
 *
 * If any of `llhttp_data_cb` returns errno not equal to `HPE_OK` - the parsing
 * interrupts, and such errno is returned from `llhttp_execute()`. If
 * `HPE_PAUSED` was used as a errno, the execution can be resumed with
 * `llhttp_resume()` call.
 *
 * In a special case of CONNECT/Upgrade request/response `HPE_PAUSED_UPGRADE`
 * is returned after fully parsing the request/response. If the user wishes to
 * continue parsing, they need to invoke `llhttp_resume_after_upgrade()`.
 *
 * NOTE: if this function ever returns a non-pause type error, it will continue
 * to return the same error upon each successive call up until `llhttp_init()`
 * is called.
 */
LLHTTP_EXPORT
llhttp_errno_t llhttp_execute(llhttp_t* parser, const char* data, size_t len);

/* This method should be called when the other side has no further bytes to
 * send (e.g. shutdown of readable side of the TCP connection.)
 *
 * Requests without `Content-Length` and other messages might require treating
 * all incoming bytes as the part of the body, up to the last byte of the
 * connection. This method will invoke `on_message_complete()` callback if the
 * request was terminated safely. Otherwise a error code would be returned.
 */
LLHTTP_EXPORT
llhttp_errno_t llhttp_finish(llhttp_t* parser);

/* Returns `1` if the incoming message is parsed until the last byte, and has
 * to be completed by calling `llhttp_finish()` on EOF
 */
LLHTTP_EXPORT
int llhttp_message_needs_eof(const llhttp_t* parser);

/* Returns `1` if there might be any other messages following the last that was
 * successfully parsed.
 */
LLHTTP_EXPORT
int llhttp_should_keep_alive(const llhttp_t* parser);

/* Make further calls of `llhttp_execute()` return `HPE_PAUSED` and set
 * appropriate error reason.
 *
 * Important: do not call this from user callbacks! User callbacks must return
 * `HPE_PAUSED` if pausing is required.
 */
LLHTTP_EXPORT
void llhttp_pause(llhttp_t* parser);

/* Might be called to resume the execution after the pause in user's callback.
 * See `llhttp_execute()` above for details.
 *
 * Call this only if `llhttp_execute()` returns `HPE_PAUSED`.
 */
LLHTTP_EXPORT
void llhttp_resume(llhttp_t* parser);

/* Might be called to resume the execution after the pause in user's callback.
 * See `llhttp_execute()` above for details.
 *
 * Call this only if `llhttp_execute()` returns `HPE_PAUSED_UPGRADE`
 */
LLHTTP_EXPORT
void llhttp_resume_after_upgrade(llhttp_t* parser);

/* Returns the latest return error */
LLHTTP_EXPORT
llhttp_errno_t llhttp_get_errno(const llhttp_t* parser);

/* Returns the verbal explanation of the latest returned error.
 *
 * Note: User callback should set error reason when returning the error. See
 * `llhttp_set_error_reason()` for details.
 */
LLHTTP_EXPORT
const char* llhttp_get_error_reason(const llhttp_t* parser);

/* Assign verbal description to the returned error. Must be called in user
 * callbacks right before returning the errno.
 *
 * Note: `HPE_USER` error code might be useful in user callbacks.
 */
LLHTTP_EXPORT
void llhttp_set_error_reason(llhttp_t* parser, const char* reason);

/* Returns the pointer to the last parsed byte before the returned error. The
 * pointer is relative to the `data` argument of `llhttp_execute()`.
 *
 * Note: this method might be useful for counting the number of parsed bytes.
 */
LLHTTP_EXPORT
const char* llhttp_get_error_pos(const llhttp_t* parser);

/* Returns textual name of error code */
LLHTTP_EXPORT
const char* llhttp_errno_name(llhttp_errno_t err);

/* Returns textual name of HTTP method */
LLHTTP_EXPORT
const char* llhttp_method_name(llhttp_method_t method);

/* Returns textual name of HTTP status */
LLHTTP_EXPORT
const char* llhttp_status_name(llhttp_status_t status);

/* Enables/disables lenient header value parsing (disabled by default).
 *
 * Lenient parsing disables header value token checks, extending llhttp's
 * protocol support to highly non-compliant clients/server. No
 * `HPE_INVALID_HEADER_TOKEN` will be raised for incorrect header values when
 * lenient parsing is "on".
 *
 * **Enabling this flag can pose a security issue since you will be exposed to
 * request smuggling attacks. USE WITH CAUTION!**
 */
LLHTTP_EXPORT
void llhttp_set_lenient_headers(llhttp_t* parser, int enabled);


/* Enables/disables lenient handling of conflicting `Transfer-Encoding` and
 * `Content-Length` headers (disabled by default).
 *
 * Normally `llhttp` would error when `Transfer-Encoding` is present in
 * conjunction with `Content-Length`. This error is important to prevent HTTP
 * request smuggling, but may be less desirable for small number of cases
 * involving legacy servers.
 *
 * **Enabling this flag can pose a security issue since you will be exposed to
 * request smuggling attacks. USE WITH CAUTION!**
 */
LLHTTP_EXPORT
void llhttp_set_lenient_chunked_length(llhttp_t* parser, int enabled);


/* Enables/disables lenient handling of `Connection: close` and HTTP/1.0
 * requests responses.
 *
 * Normally `llhttp` would error on (in strict mode) or discard (in loose mode)
 * the HTTP request/response after the request/response with `Connection: close`
 * and `Content-Length`. This is important to prevent cache poisoning attacks,
 * but might interact badly with outdated and insecure clients. With this flag
 * the extra request/response will be parsed normally.
 *
 * **Enabling this flag can pose a security issue since you will be exposed to
 * poisoning attacks. USE WITH CAUTION!**
 */
LLHTTP_EXPORT
void llhttp_set_lenient_keep_alive(llhttp_t* parser, int enabled);

/* Enables/disables lenient handling of `Transfer-Encoding` header.
 *
 * Normally `llhttp` would error when a `Transfer-Encoding` has `chunked` value
 * and another value after it (either in a single header or in multiple
 * headers whose value are internally joined using `, `).
 * This is mandated by the spec to reliably determine request body size and thus
 * avoid request smuggling.
 * With this flag the extra value will be parsed normally.
 *
 * **Enabling this flag can pose a security issue since you will be exposed to
 * request smuggling attacks. USE WITH CAUTION!**
 */
LLHTTP_EXPORT
void llhttp_set_lenient_transfer_encoding(llhttp_t* parser, int enabled);

/* Enables/disables lenient handling of HTTP version.
 *
 * Normally `llhttp` would error when the HTTP version in the request or status line
 * is not `0.9`, `1.0`, `1.1` or `2.0`.
 * With this flag the invalid value will be parsed normally.
 *
 * **Enabling this flag can pose a security issue since you will allow unsupported
 * HTTP versions. USE WITH CAUTION!**
 */
LLHTTP_EXPORT
void llhttp_set_lenient_version(llhttp_t* parser, int enabled);

/* Enables/disables lenient handling of additional data received after a message ends
 * and keep-alive is disabled.
 *
 * Normally `llhttp` would error when additional unexpected data is received if the message
 * contains the `Connection` header with `close` value.
 * With this flag the extra data will discarded without throwing an error.
 *
 * **Enabling this flag can pose a security issue since you will be exposed to
 * poisoning attacks. USE WITH CAUTION!**
 */
LLHTTP_EXPORT
void llhttp_set_lenient_data_after_close(llhttp_t* parser, int enabled);

/* Enables/disables lenient handling of incomplete CRLF sequences.
 *
 * Normally `llhttp` would error when a CR is not followed by LF when terminating the
 * request line, the status line, the headers or a chunk header.
 * With this flag only a CR is required to terminate such sections.
 *
 * **Enabling this flag can pose a security issue since you will be exposed to
 * request smuggling attacks. USE WITH CAUTION!**
 */
LLHTTP_EXPORT
void llhttp_set_lenient_optional_lf_after_cr(llhttp_t* parser, int enabled);

/*
 * Enables/disables lenient handling of line separators.
 *
 * Normally `llhttp` would error when a LF is not preceded by CR when terminating the
 * request line, the status line, the headers, a chunk header or a chunk data.
 * With this flag only a LF is required to terminate such sections.
 *
 * **Enabling this flag can pose a security issue since you will be exposed to
 * request smuggling attacks. USE WITH CAUTION!**
 */
LLHTTP_EXPORT
void llhttp_set_lenient_optional_cr_before_lf(llhttp_t* parser, int enabled);

/* Enables/disables lenient handling of chunks not separated via CRLF.
 *
 * Normally `llhttp` would error when after a chunk data a CRLF is missing before
 * starting a new chunk.
 * With this flag the new chunk can start immediately after the previous one.
 *
 * **Enabling this flag can pose a security issue since you will be exposed to
 * request smuggling attacks. USE WITH CAUTION!**
 */
LLHTTP_EXPORT
void llhttp_set_lenient_optional_crlf_after_chunk(llhttp_t* parser, int enabled);

/* Enables/disables lenient handling of spaces after chunk size.
 *
 * Normally `llhttp` would error when after a chunk size is followed by one or more
 * spaces are present instead of a CRLF or `;`.
 * With this flag this check is disabled.
 *
 * **Enabling this flag can pose a security issue since you will be exposed to
 * request smuggling attacks. USE WITH CAUTION!**
 */
LLHTTP_EXPORT
void llhttp_set_lenient_spaces_after_chunk_size(llhttp_t* parser, int enabled);

/* Enables/disables relaxed handling of unusual characters in header values.
 *
 * RFC 9110 describes NULL, CR and LF as 'dangerous' and says they MUST be
 * rejected, while other control characters are merely 'invalid' and discouraged,
 * and are explicitly allowed by other standards (e.g. WHATWG Fetch) and
 * in surprisingly common use on the web.
 *
 * This flag enables these 'invalid but common' characters, aiming to
 * maximize compatibility without enabling any potentially dangerous scenarios.
 *
 * Unlike `llhttp_set_lenient_headers()`, this does NOT enable any other
 * potentially unsafe behaviors (like accepting whitespace before colons
 * or after the start line).
 */
LLHTTP_EXPORT
void llhttp_set_lenient_header_value_relaxed(llhttp_t* parser, int enabled);

#ifdef __cplusplus
}  /* extern "C" */
#endif
#endif  /* INCLUDE_LLHTTP_API_H_ */


#endif  /* INCLUDE_LLHTTP_H_ */

// === test/cbmc/include/core_http_config.h (verbatim from upstream) ===
/*
 * coreHTTP
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file core_http_config.h
 * @brief Custom configurations for the coreHTTP library.
 */

#ifndef CORE_HTTP_CONFIG_H
#define CORE_HTTP_CONFIG_H

/**
 * @brief The maximum duration between non-empty network reads while receiving
 * an HTTP response via the #HTTPClient_Send API function.
 *
 * The transport receive function may be called multiple times until the end of
 * the response is detected by the parser. This timeout represents the maximum
 * duration that is allowed without any data reception from the network for the
 * incoming response.
 *
 * If the timeout expires, the #HTTPClient_Send function will return
 * #HTTPNetworkError.
 *
 * This is set to 1 to exit right away after a zero is received in the transport
 * receive stub. There is no added value, in proving memory safety, to repeat
 * the logic that checks if the retry timeout is reached.
 */
#define HTTP_RECV_RETRY_TIMEOUT_MS    ( 1U )

/**
 * @brief The maximum duration between non-empty network transmissions while
 * sending an HTTP request via the #HTTPClient_Send API function.
 *
 * When sending an HTTP request, the transport send function may be called multiple
 * times until all of the required number of bytes are sent.
 * This timeout represents the maximum duration that is allowed for no data
 * transmission over the network through the transport send function.
 *
 * If the timeout expires, the #HTTPClient_Send function returns #HTTPNetworkError.
 *
 * This is set to 1 to exit right away after a zero is received in the transport
 * send stub. There is no added value, in proving memory safety, to repeat
 * the logic that checks if the retry timeout is reached.
 */
#define HTTP_SEND_RETRY_TIMEOUT_MS    ( 1U )


#endif /* ifndef CORE_HTTP_CONFIG_H */

// === source/interface/transport_interface.h (verbatim from upstream) ===
/*
 * coreHTTP
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file transport_interface.h
 * @brief Transport interface definitions to send and receive data over the
 * network.
 */
#ifndef TRANSPORT_INTERFACE_H_
#define TRANSPORT_INTERFACE_H_

#include <stdint.h>
#include <stddef.h>

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/**
 * @transportpage
 * @brief The transport interface definition.
 *
 * @transportsectionoverview
 *
 * The transport interface is a set of APIs that must be implemented using an
 * external transport layer protocol. The transport interface is defined in
 * @ref transport_interface.h. This interface allows protocols like MQTT and
 * HTTP to send and receive data over the transport layer. This
 * interface does not handle connection and disconnection to the server of
 * interest. The connection, disconnection, and other transport settings, like
 * timeout and TLS setup, must be handled in the user application.
 * <br>
 *
 * The functions that must be implemented are:<br>
 * - [Transport Receive](@ref TransportRecv_t)
 * - [Transport Send](@ref TransportSend_t)
 *
 * Each of the functions above take in an opaque context @ref NetworkContext_t.
 * The functions above and the context are also grouped together in the
 * @ref TransportInterface_t structure:<br><br>
 * @snippet this define_transportinterface
 * <br>
 *
 * @transportsectionimplementation
 *
 * The following steps give guidance on implementing the transport interface:
 *
 * -# Implementing @ref NetworkContext_t<br><br>
 * @snippet this define_networkcontext
 * <br>
 * @ref NetworkContext_t is the incomplete type <b>struct NetworkContext</b>.
 * The implemented struct NetworkContext must contain all of the information
 * that is needed to receive and send data with the @ref TransportRecv_t
 * and the @ref TransportSend_t implementations.<br>
 * In the case of TLS over TCP, struct NetworkContext is typically implemented
 * with the TCP socket context and a TLS context.<br><br>
 * <b>Example code:</b>
 * @code{c}
 * struct NetworkContext
 * {
 *     struct MyTCPSocketContext tcpSocketContext;
 *     struct MyTLSContext tlsContext;
 * };
 * @endcode
 * <br>
 * -# Implementing @ref TransportRecv_t<br><br>
 * @snippet this define_transportrecv
 * <br>
 * This function is expected to populate a buffer, with bytes received from the
 * transport, and return the number of bytes placed in the buffer.
 * In the case of TLS over TCP, @ref TransportRecv_t is typically implemented by
 * calling the TLS layer function to receive data. In case of plaintext TCP
 * without TLS, it is typically implemented by calling the TCP layer receive
 * function. @ref TransportRecv_t may be invoked multiple times by the protocol
 * library, if fewer bytes than were requested to receive are returned.
 * Please note that it is HIGHLY RECOMMENDED that the transport receive implementation does NOT block.
 * <br><br>
 * <b>Example code:</b>
 * @code{c}
 * int32_t myNetworkRecvImplementation( NetworkContext_t * pNetworkContext,
 *                                      void * pBuffer,
 *                                      size_t bytesToRecv )
 * {
 *     int32_t bytesReceived = 0;
 *     bool callTlsRecvFunc = true;
 *
 *     // For a single byte read request, check if data is available on the network.
 *     if( bytesToRecv == 1 )
 *     {
 *        // If no data is available on the network, do not call TLSRecv
 *        // to avoid blocking for socket timeout.
 *        if( TLSRecvCount( pNetworkContext->tlsContext ) == 0 )
 *        {
 *            callTlsRecvFunc = false;
 *        }
 *     }
 *
 *     if( callTlsRecvFunc == true )
 *     {
 *        bytesReceived = TLSRecv( pNetworkContext->tlsContext,
 *                                 pBuffer,
 *                                 bytesToRecv,
 *                                 MY_SOCKET_TIMEOUT );
 *        if( bytesReceived < 0 )
 *        {
 *           // If the error code represents a timeout, then the return
 *           // code should be translated to zero so that the caller
 *           // can retry the read operation.
 *           if( bytesReceived == MY_SOCKET_ERROR_TIMEOUT )
 *           {
 *              bytesReceived = 0;
 *           }
 *        }
 *        // Handle other cases.
 *     }
 *     return bytesReceived;
 * }
 * @endcode
 * <br>
 * -# Implementing @ref TransportSend_t<br><br>
 * @snippet this define_transportsend
 * <br>
 * This function is expected to send the bytes, in the given buffer over the
 * transport, and return the number of bytes sent.
 * In the case of TLS over TCP, @ref TransportSend_t is typically implemented by
 * calling the TLS layer function to send data. In case of plaintext TCP
 * without TLS, it is typically implemented by calling the TCP layer send
 * function. @ref TransportSend_t may be invoked multiple times by the protocol
 * library, if fewer bytes than were requested to send are returned.
 * <br><br>
 * <b>Example code:</b>
 * @code{c}
 * int32_t myNetworkSendImplementation( NetworkContext_t * pNetworkContext,
 *                                      const void * pBuffer,
 *                                      size_t bytesToSend )
 * {
 *     int32_t bytesSent = 0;
 *     bytesSent = TLSSend( pNetworkContext->tlsContext,
 *                          pBuffer,
 *                          bytesToSend,
 *                          MY_SOCKET_TIMEOUT );
 *
 *      // If underlying TCP buffer is full, set the return value to zero
 *      // so that caller can retry the send operation.
 *     if( bytesSent == MY_SOCKET_ERROR_BUFFER_FULL )
 *     {
 *          bytesSent = 0;
 *     }
 *     else if( bytesSent < 0 )
 *     {
 *         // Handle socket error.
 *     }
 *     // Handle other cases.
 *
 *     return bytesSent;
 * }
 * @endcode
 */

/**
 * @transportstruct
 * @typedef NetworkContext_t
 * @brief The NetworkContext is an incomplete type. An implementation of this
 * interface must define struct NetworkContext for the system requirements.
 * This context is passed into the network interface functions.
 */
/* @[define_networkcontext] */
struct NetworkContext;
typedef struct NetworkContext NetworkContext_t;
/* @[define_networkcontext] */

/**
 * @transportcallback
 * @brief Transport interface for receiving data on the network.
 *
 * @note It is HIGHLY RECOMMENDED that the transport receive
 * implementation does NOT block.
 * coreMQTT will continue to call the transport interface if it receives
 * a partial packet until it accumulates enough data to get the complete
 * MQTT packet.
 * A non‐blocking implementation is also essential so that the library's inbuilt
 * keep‐alive mechanism can work properly, given the user chooses to use
 * that over their own keep alive mechanism.
 *
 * @param[in] pNetworkContext Implementation-defined network context.
 * @param[in] pBuffer Buffer to receive the data into.
 * @param[in] bytesToRecv Number of bytes requested from the network.
 *
 * @return The number of bytes received or a negative value to indicate
 * error.
 *
 * @note If no data is available on the network to read and no error
 * has occurred, zero MUST be the return value. A zero return value
 * SHOULD represent that the read operation can be retried by calling
 * the API function. Zero MUST NOT be returned if a network disconnection
 * has occurred.
 */
/* @[define_transportrecv] */
typedef int32_t ( * TransportRecv_t )( NetworkContext_t * pNetworkContext,
                                       void * pBuffer,
                                       size_t bytesToRecv );
/* @[define_transportrecv] */

/**
 * @transportcallback
 * @brief Transport interface for sending data over the network.
 *
 * @param[in] pNetworkContext Implementation-defined network context.
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToSend Number of bytes to send over the network.
 *
 * @return The number of bytes sent or a negative value to indicate error.
 *
 * @note If no data is transmitted over the network due to a full TX buffer and
 * no network error has occurred, this MUST return zero as the return value.
 * A zero return value SHOULD represent that the send operation can be retried
 * by calling the API function. Zero MUST NOT be returned if a network disconnection
 * has occurred.
 */
/* @[define_transportsend] */
typedef int32_t ( * TransportSend_t )( NetworkContext_t * pNetworkContext,
                                       const void * pBuffer,
                                       size_t bytesToSend );
/* @[define_transportsend] */

/**
 * @brief Transport vector structure for sending multiple messages.
 */
typedef struct TransportOutVector
{
    /**
     * @brief Base address of data.
     */
    const void * iov_base;

    /**
     * @brief Length of data in buffer.
     */
    size_t iov_len;
} TransportOutVector_t;

/**
 * @transportcallback
 * @brief Transport interface function for "vectored" / scatter-gather based
 * writes. This function is expected to iterate over the list of vectors pIoVec
 * having ioVecCount entries containing portions of one MQTT message at a maximum.
 * If the proper functionality is available, then the data in the list should be
 * copied to the underlying TCP buffer before flushing the buffer. Implementing it
 * in this fashion  will lead to sending of fewer TCP packets for all the values
 * in the list.
 *
 * @note If the proper write functionality is not present for a given device/IP-stack,
 * then there is no strict requirement to implement write. Only the send and recv
 * interfaces must be defined for the application to work properly.
 *
 * @param[in] pNetworkContext Implementation-defined network context.
 * @param[in] pIoVec An array of TransportIoVector_t structs.
 * @param[in] ioVecCount Number of TransportIoVector_t in pIoVec.
 *
 * @return The number of bytes written or a negative value to indicate error.
 *
 * @note If no data is written to the buffer due to the buffer being full this MUST
 * return zero as the return value.
 * A zero return value SHOULD represent that the write operation can be retried
 * by calling the API function. Zero MUST NOT be returned if a network disconnection
 * has occurred.
 */
/* @[define_transportwritev] */
typedef int32_t ( * TransportWritev_t )( NetworkContext_t * pNetworkContext,
                                         TransportOutVector_t * pIoVec,
                                         size_t ioVecCount );
/* @[define_transportwritev] */

/**
 * @transportstruct
 * @brief The transport layer interface.
 */
/* @[define_transportinterface] */
typedef struct TransportInterface
{
    TransportRecv_t recv;               /**< Transport receive function pointer. */
    TransportSend_t send;               /**< Transport send function pointer. */
    TransportWritev_t writev;           /**< Transport writev function pointer. */
    NetworkContext_t * pNetworkContext; /**< Implementation-defined network context. */
} TransportInterface_t;
/* @[define_transportinterface] */

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef TRANSPORT_INTERFACE_H_ */

// === source/include/core_http_client.h (verbatim from upstream) ===
/*
 * coreHTTP
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file core_http_client.h
 * @brief User facing functions of the HTTP Client library.
 */

#ifndef CORE_HTTP_CLIENT_H_
#define CORE_HTTP_CLIENT_H_

#include <stdint.h>
#include <stddef.h>

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/**
 * @cond DOXYGEN_IGNORE
 * The current version of this library.
 *
 * If HTTP_LIBRARY_VERSION ends with + it represents the version in development
 * after the numbered release.
 */
#define HTTP_LIBRARY_VERSION    "v3.1.3"
/** @endcond */

/* HTTP_DO_NOT_USE_CUSTOM_CONFIG allows building the HTTP Client library
 * without a config file. If a config file is provided, the
 * HTTP_DO_NOT_USE_CUSTOM_CONFIG macro must not be defined.
 */
#ifndef HTTP_DO_NOT_USE_CUSTOM_CONFIG

#endif

/* Include config defaults header to get default values of configurations not
 * defined in core_http_config.h file. */

/* Transport interface include. */

/* Convenience macros for some HTTP request methods. */

/** @addtogroup http_constants
 *  @{
 */
#define HTTP_METHOD_GET     "GET"                       /**< HTTP Method GET string. */
#define HTTP_METHOD_PUT     "PUT"                       /**< HTTP Method PUT string. */
#define HTTP_METHOD_POST    "POST"                      /**< HTTP Method POST string. */
#define HTTP_METHOD_HEAD    "HEAD"                      /**< HTTP Method HEAD string. */
/** @}*/

/**
 * @ingroup http_constants
 * @brief The maximum Content-Length header field and value that could be
 * written to the request header buffer.
 */
#define HTTP_MAX_CONTENT_LENGTH_HEADER_LENGTH    sizeof( "Content-Length: 4294967295" ) - 1U

/**
 * @defgroup http_send_flags HTTPClient_Send Flags
 * @brief Values for #HTTPClient_Send sendFlags parameter.
 * These flags control some behavior of sending the request or receiving the
 * response.
 *
 * Flags should be bitwise-ORed with each other to change the behavior of
 * #HTTPClient_Send.
 */

/**
 * @ingroup http_send_flags
 * @brief Set this flag to disable automatically writing the Content-Length
 * header to send to the server.
 *
 * This flag is valid only for #HTTPClient_Send sendFlags parameter.
 */
#define HTTP_SEND_DISABLE_CONTENT_LENGTH_FLAG    0x1U

/**
 * @defgroup http_request_flags HTTPRequestInfo_t Flags
 * @brief Flags for #HTTPRequestInfo_t.reqFlags.
 * These flags control what headers are written or not to the
 * #HTTPRequestHeaders_t.pBuffer by #HTTPClient_InitializeRequestHeaders.
 *
 * Flags should be bitwise-ORed with each other to change the behavior of
 * #HTTPClient_InitializeRequestHeaders.
 */

/**
 * @ingroup http_request_flags
 * @brief Set this flag to indicate that the request is for a persistent
 * connection.
 *
 * Setting this will cause a "Connection: Keep-Alive" to be written to the
 * request headers.
 *
 * This flag is valid only for #HTTPRequestInfo_t reqFlags parameter.
 */
#define HTTP_REQUEST_KEEP_ALIVE_FLAG       0x1U

/**
 * @ingroup http_request_flags
 * @brief Set this flag to skip the User-Agent in the request headers.
 *
 * Setting this will cause the "User-Agent: <Value>" to be omitted in the
 * request headers.
 *
 * This flag is valid only for #HTTPRequestInfo_t reqFlags parameter.
 */
#define HTTP_REQUEST_NO_USER_AGENT_FLAG    0x2U

/**
 * @defgroup http_response_flags HTTPResponse_t Flags
 * @brief Flags for #HTTPResponse_t.respFlags.
 * These flags are populated in #HTTPResponse_t.respFlags by the #HTTPClient_Send
 * function.
 *
 * A flag's value can be extracted from #HTTPResponse_t.respFlags with a
 * bitwise-AND.
 */

/**
 * @ingroup http_response_flags
 * @brief This will be set to true if header "Connection: close" is found.
 *
 * If a "Connection: close" header is present the application should always
 * close the connection.
 *
 * This flag is valid only for #HTTPResponse_t.respFlags.
 */
#define HTTP_RESPONSE_CONNECTION_CLOSE_FLAG         0x1U

/**
 * @ingroup http_response_flags
 * @brief This will be set to true if header "Connection: Keep-Alive" is found.
 *
 * This flag is valid only for #HTTPResponse_t.respFlags.
 */
#define HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG    0x2U

/**
 * @defgroup http_response_option_flags HTTPResponse_t Flags
 * @brief Flags for #HTTPResponse_t.respOptionFlags.
 * These flags control the behavior of response parsing.
 *
 * Flags should be bitwise-ORed with each other to change the behavior of
 * #HTTPClient_ReceiveAndParseHttpResponse and #HTTPClient_Send.
 */

/**
 * @ingroup http_response_option_flags
 * @brief Set this flag to indicate that the response body should not be parsed.
 *
 * Setting this will cause parser to stop after parsing the headers. Portion of
 * the raw body may be available in #HTTPResponse_t.pBody and
 * #HTTPResponse_t.bodyLen.
 *
 * This flag is valid only for #HTTPResponse_t.respOptionFlags.
 */
#define HTTP_RESPONSE_DO_NOT_PARSE_BODY_FLAG    0x1U

/**
 * @ingroup http_constants
 * @brief Flag that represents End of File byte in the range specification of
 * a Range Request.
 * This flag should be used ONLY for 2 kinds of range specifications when
 * creating the Range Request header through the #HTTPClient_AddRangeHeader
 * function:
 *  - When the requested range is all bytes from the starting range byte to
 * the end of file.
 *  - When the requested range is for the last N bytes of the file.
 * In both cases, this value should be used for the "rangeEnd" parameter.
 */
#define HTTP_RANGE_REQUEST_END_OF_FILE          -1

/**
 * @ingroup http_enum_types
 * @brief The HTTP Client library return status.
 */
typedef enum HTTPStatus
{
    /**
     * @brief The HTTP Client library function completed successfully.
     *
     * Functions that may return this value:
     * - #HTTPClient_InitializeRequestHeaders
     * - #HTTPClient_AddHeader
     * - #HTTPClient_AddRangeHeader
     * - #HTTPClient_Send
     * - #HTTPClient_ReadHeader
     */
    HTTPSuccess,

    /**
     * @brief The HTTP Client library function input an invalid parameter.
     *
     * Functions that may return this value:
     * - #HTTPClient_InitializeRequestHeaders
     * - #HTTPClient_AddHeader
     * - #HTTPClient_AddRangeHeader
     * - #HTTPClient_Send
     * - #HTTPClient_ReadHeader
     */
    HTTPInvalidParameter,

    /**
     * @brief A network error was returned from the transport interface.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTPNetworkError,

    /**
     * @brief Part of the HTTP response was received from the network.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTPPartialResponse,

    /**
     * @brief No HTTP response was received from the network.
     *
     * This can occur only if there was no data received from the transport
     * interface.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTPNoResponse,

    /**
     * @brief The application buffer was not large enough for the HTTP request
     * headers or the HTTP response message.
     *
     * Functions that may return this value:
     * - #HTTPClient_InitializeRequestHeaders
     * - #HTTPClient_AddHeader
     * - #HTTPClient_AddRangeHeader
     * - #HTTPClient_Send
     */
    HTTPInsufficientMemory,

    /**
     * @brief A response contained the "Connection: close" header, but there
     * was more data at the end of the complete message.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTPSecurityAlertExtraneousResponseData,

    /**
     * @brief The server sent a chunk header containing an invalid character.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTPSecurityAlertInvalidChunkHeader,

    /**
     * @brief The server sent a response with an invalid character in the
     * HTTP protocol version.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTPSecurityAlertInvalidProtocolVersion,

    /**
     * @brief The server sent a response with an invalid character in the
     * HTTP status-code or the HTTP status code is out of range.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTPSecurityAlertInvalidStatusCode,

    /**
     * @brief An invalid character was found in the HTTP response message or in
     * the HTTP request header.
     *
     * Functions that may return this value:
     * - #HTTPClient_AddHeader
     * - #HTTPClient_Send
     */
    HTTPSecurityAlertInvalidCharacter,

    /**
     * @brief The response contains either an invalid character in the
     * Content-Length header or a Content-Length header when it was not expected
     * to be present.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTPSecurityAlertInvalidContentLength,

    /**
     * @brief Represents the paused state of the HTTP parser.
     *
     * This state indicates that the parser has encountered a pause condition
     * and is waiting for further input.
     *
     * @see HTTPClient_Send
     * @see HTTPClient_ReceiveAndParseHttpResponse
     */
    HTTPParserPaused,

    /**
     * @brief An error occurred in the third-party parsing library.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     * - #HTTPClient_ReadHeader
     */
    HTTPParserInternalError,

    /**
     * @brief The requested header field was not found in the response buffer.
     *
     * Functions that may return this value:
     * - #HTTPClient_ReadHeader
     */
    HTTPHeaderNotFound,

    /**
     * @brief The HTTP response, provided for parsing, is either corrupt or
     * incomplete.
     *
     * Functions that may return this value:
     * - #HTTPClient_ReadHeader
     */
    HTTPInvalidResponse
} HTTPStatus_t;

/**
 * @ingroup http_struct_types
 * @brief Represents header data that will be sent in an HTTP request.
 *
 * The memory for the header data buffer is supplied by the user. Information in
 * the buffer will be filled by calling #HTTPClient_InitializeRequestHeaders and
 * #HTTPClient_AddHeader. This buffer may be automatically filled with the
 * Content-Length header in #HTTPClient_Send, please see
 * HTTP_MAX_CONTENT_LENGTH_HEADER_LENGTH for the maximum amount of space needed
 * to accommodate the Content-Length header.
 */
typedef struct HTTPRequestHeaders
{
    /**
     * @brief Buffer to hold the raw HTTP request headers.
     *
     * This buffer is supplied by the application.
     *
     * This buffer is owned by the library during #HTTPClient_AddHeader,
     * #HTTPClient_AddRangeHeader, #HTTPClient_InitializeRequestHeaders, and
     * #HTTPClient_Send. This buffer should not be modified until
     * after these functions return.
     *
     * For optimization this buffer may be re-used with the response. The user
     * can re-use this buffer for the storing the response from the server in
     * #HTTPResponse_t.pBuffer.
     */
    uint8_t * pBuffer;
    size_t bufferLen; /**< The length of pBuffer in bytes. */

    /**
     * @brief The actual size in bytes of headers in the buffer. This field
     * is updated by the HTTP Client library functions #HTTPClient_AddHeader,
     * and #HTTPClient_InitializeRequestHeaders.
     */
    size_t headersLen;
} HTTPRequestHeaders_t;

/**
 * @ingroup http_struct_types
 * @brief Configurations of the initial request headers.
 */
typedef struct HTTPRequestInfo
{
    /**
     * @brief The HTTP request method e.g. "GET", "POST", "PUT", or "HEAD".
     */
    const char * pMethod;
    size_t methodLen; /**< The length of the method in bytes. */

    /**
     * @brief The Request-URI to the objects of interest, e.g. "/path/to/item.txt".
     */
    const char * pPath;
    size_t pathLen; /**< The length of the path in bytes. */

    /**
     * @brief The server's host name, e.g. "my-storage.my-cloud.com".
     *
     * The host does not have a "https://" or "http://" prepending.
     */
    const char * pHost;
    size_t hostLen; /**< The length of the host in bytes. */

    /**
     * @brief Flags to activate other request header configurations.
     *
     * Please see @ref http_request_flags for more information.
     */
    uint32_t reqFlags;
} HTTPRequestInfo_t;



/**
 * @ingroup http_struct_types
 * @brief Callback to intercept headers during the first parse through of the
 * response as it is received from the network.
 */
typedef struct HTTPClient_ResponseHeaderParsingCallback
{
    /**
     * @brief Invoked when both a header field and its associated header value are found.
     * @param[in] pContext User context.
     * @param[in] fieldLoc Location of the header field name in the response buffer.
     * @param[in] fieldLen Length in bytes of the field name.
     * @param[in] valueLoc Location of the header value in the response buffer.
     * @param[in] valueLen Length in bytes of the value.
     * @param[in] statusCode The HTTP response status-code.
     */
    void ( * onHeaderCallback )( void * pContext,
                                 const char * fieldLoc,
                                 size_t fieldLen,
                                 const char * valueLoc,
                                 size_t valueLen,
                                 uint16_t statusCode );

    /**
     * @brief Private context for the application.
     */
    void * pContext;
} HTTPClient_ResponseHeaderParsingCallback_t;

/**
 * @ingroup http_callback_types
 * @brief Application provided function to query the current time in
 * milliseconds.
 *
 * @return The current time in milliseconds.
 */
typedef uint32_t (* HTTPClient_GetCurrentTimeFunc_t )( void );

/**
 * @ingroup http_struct_types
 * @brief Represents an HTTP response.
 */
typedef struct HTTPResponse
{
    /**
     * @brief Buffer for both the raw HTTP header and body.
     *
     * This buffer is supplied by the application.
     *
     * This buffer is owned by the library during #HTTPClient_Send and
     * #HTTPClient_ReadHeader. This buffer should not be modified until after
     * these functions return.
     *
     * For optimization this buffer may be used with the request headers. The
     * request header buffer is configured in #HTTPRequestHeaders_t.pBuffer.
     * When the same buffer is used for the request headers, #HTTPClient_Send
     * will send the headers in the buffer first, then fill the buffer with
     * the response message.
     */
    uint8_t * pBuffer;
    size_t bufferLen; /**< The length of the response buffer in bytes. */

    /**
     * @brief Optional callback for intercepting the header during the first
     * parse through of the response as is it receive from the network.
     * Set to NULL to disable.
     */
    HTTPClient_ResponseHeaderParsingCallback_t * pHeaderParsingCallback;

    /**
     * @brief Optional callback for getting the system time.
     *
     * This is used to calculate the elapsed time when retrying network reads or
     * sends that return zero bytes received or sent, respectively. If this
     * field is set to NULL, then network send and receive won't be retried
     * after a zero is returned.
     *
     * If this function is set, then the maximum time for retrying network reads
     * that return zero bytes can be set through #HTTP_RECV_RETRY_TIMEOUT_MS.
     *
     * If this function is set, then the maximum elapsed time between network
     * sends greater than zero is set in HTTP_SEND_RETRY_TIMEOUT_MS.
     */
    HTTPClient_GetCurrentTimeFunc_t getTime;

    /**
     * @brief The starting location of the response headers in pBuffer.
     *
     * This is updated by #HTTPClient_Send.
     */
    const uint8_t * pHeaders;

    /**
     * @brief Byte length of the response headers in pBuffer.
     *
     * This is updated by #HTTPClient_Send.
     */
    size_t headersLen;

    /**
     * @brief The starting location of the response body in pBuffer.
     *
     * This is updated by #HTTPClient_Send.
     */
    const uint8_t * pBody;

    /**
     * @brief Byte length of the body in pBuffer.
     *
     * This is updated by #HTTPClient_Send.
     */
    size_t bodyLen;

    /* Useful HTTP header values found. */

    /**
     * @brief The HTTP response Status-Code.
     *
     * This is updated by #HTTPClient_Send.
     */
    uint16_t statusCode;

    /**
     * @brief The value in the "Content-Length" header is returned here.
     *
     * This is updated by #HTTPClient_Send.
     */
    size_t contentLength;

    /**
     * @brief Count of the headers sent by the server.
     *
     * This is updated by #HTTPClient_Send.
     */
    size_t headerCount;

    /**
     * @brief Indicates whether the HTTP response headers have been fully received.
     *
     * This variable is set to 1 after all headers have been received and processed by #HTTPClient_Send.
     */
    uint8_t areHeadersComplete;

    /**
     * @brief Flags to control the behavior of response parsing.
     *
     * Please see @ref http_response_option_flags for more information.
     */
    uint32_t respOptionFlags;

    /**
     * @brief Flags of useful headers found in the response.
     *
     * This is updated by #HTTPClient_Send. Please see @ref http_response_flags
     * for more information.
     */
    uint32_t respFlags;
} HTTPResponse_t;

/**
 * @brief Initialize the request headers, stored in
 * #HTTPRequestHeaders_t.pBuffer, with initial configurations from
 * #HTTPRequestInfo_t. This method is expected to be called before sending a
 * new request.
 *
 * Upon return, #HTTPRequestHeaders_t.headersLen will be updated with the number
 * of bytes written.
 *
 * Each line in the header is listed below and written in this order:
 *     <#HTTPRequestInfo_t.pMethod> <#HTTPRequestInfo_t.pPath> <#HTTP_PROTOCOL_VERSION>
 *     User-Agent: <#HTTP_USER_AGENT_VALUE>
 *     Host: <#HTTPRequestInfo_t.pHost>
 *
 * Note that "Connection" header can be added and set to "keep-alive" by
 * activating the HTTP_REQUEST_KEEP_ALIVE_FLAG in #HTTPRequestInfo_t.reqFlags.
 *
 * @param[in] pRequestHeaders Request header buffer information.
 * @param[in] pRequestInfo Initial request header configurations.
 * @return One of the following:
 * - #HTTPSuccess (If successful)
 * - #HTTPInvalidParameter (If any provided parameters or their members are invalid.)
 * - #HTTPInsufficientMemory (If provided buffer size is not large enough to hold headers.)
 *
 * **Example**
 * @code{c}
 * HTTPStatus_t httpLibraryStatus = HTTPSuccess;
 * // Declare an HTTPRequestHeaders_t and HTTPRequestInfo_t.
 * HTTPRequestHeaders_t requestHeaders = { 0 };
 * HTTPRequestInfo_t requestInfo = { 0 };
 * // A buffer that will fit the Request-Line, the User-Agent header line, and
 * // the Host header line.
 * uint8_t requestHeaderBuffer[ 256 ] = { 0 };
 *
 * // Set a buffer to serialize request headers to.
 * requestHeaders.pBuffer = requestHeaderBuffer;
 * requestHeaders.bufferLen = 256;
 *
 * // Set the Method, Path, and Host in the HTTPRequestInfo_t.
 * requestInfo.pMethod = HTTP_METHOD_GET;
 * requestInfo.methodLen = sizeof( HTTP_METHOD_GET ) - 1U;
 * requestInfo.pPath = "/html/rfc2616"
 * requestInfo.pathLen = sizeof( "/html/rfc2616" ) - 1U;
 * requestInfo.pHost = "tools.ietf.org"
 * requestInfo.hostLen = sizeof( "tools.ietf.org" ) - 1U;
 * requestInfo.reqFlags |= HTTP_REQUEST_KEEP_ALIVE_FLAG;
 *
 * httpLibraryStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders,
 *                                                          &requestInfo );
 * @endcode
 */
/* @[declare_httpclient_initializerequestheaders] */
HTTPStatus_t HTTPClient_InitializeRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders,
                                                  const HTTPRequestInfo_t * pRequestInfo );
/* @[declare_httpclient_initializerequestheaders] */

/**
 * @brief Add a header to the request headers stored in
 * #HTTPRequestHeaders_t.pBuffer.
 *
 * Upon return, pRequestHeaders->headersLen will be updated with the number of
 * bytes written.
 *
 * Headers are written in the following format:
 *
 * @code
 *     <field>: <value>\r\n\r\n
 * @endcode
 *
 * The trailing `\r\n` that denotes the end of the header lines is overwritten,
 * if it already exists in the buffer.
 *
 * @note This function validates only that `\r`, `\n`, and `:` are not present
 * in @p pValue or @p pField. `:` is allowed in @p pValue.
 *
 * @param[in] pRequestHeaders Request header buffer information.
 * @param[in] pField The header field name to write.
 * The data should be ISO 8859-1 (Latin-1) encoded per the HTTP standard,
 * but the API does not perform the character set validation.
 * @param[in] fieldLen The byte length of the header field name.
 * @param[in] pValue The header value to write.
 * The data should be ISO 8859-1 (Latin-1) encoded per the HTTP standard,
 * but the API does not perform the character set validation.
 * @param[in] valueLen The byte length of the header field value.
 *
 * @return One of the following:
 * - #HTTPSuccess (If successful.)
 * - #HTTPInvalidParameter (If any provided parameters or their members are invalid.)
 * - #HTTPInsufficientMemory (If application-provided buffer is not large enough to hold headers.)
 * - #HTTPSecurityAlertInvalidCharacter (If an invalid character was found in @p pField or @p pValue.)
 *
 * **Example**
 * @code{c}
 * HTTPStatus_t httpLibraryStatus = HTTPSuccess;
 * // Assume that requestHeaders has already been initialized with
 * // HTTPClient_InitializeRequestHeaders().
 * HTTPRequestHeaders_t requestHeaders;
 *
 * httpLibraryStatus = HTTPClient_AddHeader( &requestHeaders,
 *                                           "Request-Header-Field",
 *                                           sizeof( "Request-Header-Field" ) - 1U,
 *                                           "Request-Header-Value",
 *                                           sizeof("Request-Header-Value") - 1U );
 * @endcode
 */
/* @[declare_httpclient_addheader] */
HTTPStatus_t HTTPClient_AddHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                   const char * pField,
                                   size_t fieldLen,
                                   const char * pValue,
                                   size_t valueLen );
/* @[declare_httpclient_addheader] */

/**
 * @brief Add the byte range request header to the request headers store in
 * #HTTPRequestHeaders_t.pBuffer.
 *
 * For example, if requesting for the first 1kB of a file the following would be
 * written: `Range: bytes=0-1023\r\n\r\n`.
 *
 * The trailing `\r\n` that denotes the end of the header lines is overwritten,
 * if it already exists in the buffer.
 *
 * There are 3 different forms of range specification, determined by the
 * combination of @a rangeStartOrLastNBytes and @a rangeEnd parameter values:
 *
 * 1. Request containing both parameters for the byte range [rangeStart, rangeEnd]
 *    where @a rangeStartOrLastNBytes <= @a rangeEnd.
 *    Example request header line: `Range: bytes=0-1023\r\n` for requesting bytes in the range [0, 1023].<br>
 *    **Example**
 *    @code{c}
 *    HTTPStatus_t httpLibraryStatus = HTTPSuccess;
 *    // Assume that requestHeaders has already been initialized with
 *    // HTTPClient_InitializeRequestHeaders().
 *    HTTPRequestHeaders_t requestHeaders;
 *
 *    // Request for bytes 0 to 1023.
 *    httpLibraryStatus = HTTPClient_AddRangeHeader( &requestHeaders, 0, 1023 );
 *    @endcode
 *
 * 2. Request for the last N bytes, represented by @p rangeStartOrlastNbytes.
 *    @p rangeStartOrlastNbytes should be negative and @p rangeEnd should be
 *    #HTTP_RANGE_REQUEST_END_OF_FILE.
 *    Example request header line: `Range: bytes=-512\r\n` for requesting the last 512 bytes
 *    (or bytes in the range [512, 1023] for a 1KB sized file).<br>
 *    **Example**
 *    @code{c}
 *    HTTPStatus_t httpLibraryStatus = HTTPSuccess;
 *    // Assume that requestHeaders has already been initialized with
 *    // HTTPClient_InitializeRequestHeaders().
 *    HTTPRequestHeaders_t requestHeaders;
 *
 *    // Request for the last 512 bytes.
 *    httpLibraryStatus = HTTPClient_AddRangeHeader( &requestHeaders, -512, HTTP_RANGE_REQUEST_END_OF_FILE)
 *    @endcode
 *
 * 3. Request for all bytes (till the end of byte sequence) from byte N,
 *    represented by @p rangeStartOrlastNbytes.
 *    @p rangeStartOrlastNbytes should be >= 0 and @p rangeEnd should be
 *    #HTTP_RANGE_REQUEST_END_OF_FILE.<br>
 *    Example request header line: `Range: bytes=256-\r\n` for requesting all bytes after and
 *    including byte 256 (or bytes in the range [256,1023] for a 1kB sized file).<br>
 *    **Example**
 *    @code{c}
 *    HTTPStatus_t httpLibraryStatus = HTTPSuccess;
 *    // Assume that requestHeaders has already been initialized with
 *    // HTTPClient_InitializeRequestHeaders().
 *    HTTPRequestHeaders_t requestHeaders;
 *
 *    // Request for all bytes from byte 256 onward.
 *    httpLibraryStatus = HTTPClient_AddRangeHeader( &requestHeaders, 256, HTTP_RANGE_REQUEST_END_OF_FILE)
 *    @endcode
 *
 * @param[in] pRequestHeaders Request header buffer information.
 * @param[in] rangeStartOrlastNbytes Represents either the starting byte
 * for a range OR the last N number of bytes in the requested file.
 * @param[in] rangeEnd The ending range for the requested file. For end of file
 * byte in Range Specifications 2. and 3., #HTTP_RANGE_REQUEST_END_OF_FILE
 * should be passed.
 *
 * @return Returns the following status codes:
 * #HTTPSuccess, if successful.
 * #HTTPInvalidParameter, if input parameters are invalid, including when
 * the @p rangeStartOrlastNbytes and @p rangeEnd parameter combination is invalid.
 * #HTTPInsufficientMemory, if the passed #HTTPRequestHeaders_t.pBuffer
 * contains insufficient remaining memory for storing the range request.
 */
/* @[declare_httpclient_addrangeheader] */
HTTPStatus_t HTTPClient_AddRangeHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                        int32_t rangeStartOrlastNbytes,
                                        int32_t rangeEnd );
/* @[declare_httpclient_addrangeheader] */

/**
 * @brief Send the request headers in @p pRequestHeaders over the transport.
 *
 * If #HTTP_SEND_DISABLE_CONTENT_LENGTH_FLAG is not set in parameter @p sendFlags,
 * then the Content-Length to be sent to the server is automatically written to
 * @p pRequestHeaders. The Content-Length will not be written when there is
 * no request body. If there is not enough room in the buffer to write the
 * Content-Length then #HTTPInsufficientMemory is returned. Please see
 * #HTTP_MAX_CONTENT_LENGTH_HEADER_LENGTH for the maximum Content-Length header
 * field and value that could be written to the buffer.
 *
 * The application should close the connection with the server if any of the
 * following errors are returned:
 * - #HTTPSecurityAlertExtraneousResponseData
 * - #HTTPSecurityAlertInvalidChunkHeader
 * - #HTTPSecurityAlertInvalidProtocolVersion
 * - #HTTPSecurityAlertInvalidStatusCode
 * - #HTTPSecurityAlertInvalidCharacter
 * - #HTTPSecurityAlertInvalidContentLength
 *
 *
 * @param[in] pTransport Transport interface, see #TransportInterface_t for
 * more information.
 * @param[in] getTimestampMs Function to retrieve a timestamp in milliseconds.
 * @param[in] pRequestHeaders Request configuration containing the buffer of headers to
 * send.
 * @param[in] reqBodyLen The length of the request entity in bytes.
 * @param[in] sendFlags Flags which modify the behavior of this function. Please see @ref
 * http_send_flags for more information.
 *
 * @return #HTTPSuccess if successful. If there was a network error or less
 * bytes than what were specified were sent, then #HTTPNetworkError is
 * returned.
 *
 */
/* @[declare_httpclient_sendhttpheaders] */
HTTPStatus_t HTTPClient_SendHttpHeaders( const TransportInterface_t * pTransport,
                                         HTTPClient_GetCurrentTimeFunc_t getTimestampMs,
                                         HTTPRequestHeaders_t * pRequestHeaders,
                                         size_t reqBodyLen,
                                         uint32_t sendFlags );
/* @[declare_httpclient_sendhttpheaders] */

/**
 * @brief Send the request body in @p pRequestBodyBuf over the transport.
 *
 * @param[in] pTransport Transport interface, see #TransportInterface_t for
 * more information.
 * @param[in] getTimestampMs Function to retrieve a timestamp in milliseconds.
 * @param[in] pData HTTP request data to send.
 * @param[in] dataLen HTTP request data length.
 *
 * @return #HTTPSuccess if successful. If there was a network error or less
 * bytes than what were specified were sent, then #HTTPNetworkError is
 * returned.
 */
/* @[declare_httpclient_sendhttpdata] */
HTTPStatus_t HTTPClient_SendHttpData( const TransportInterface_t * pTransport,
                                      HTTPClient_GetCurrentTimeFunc_t getTimestampMs,
                                      const uint8_t * pData,
                                      size_t dataLen );
/* @[declare_httpclient_sendhttpdata] */

/**
 * @brief Send the request headers in #HTTPRequestHeaders_t.pBuffer and request
 * body in @p pRequestBodyBuf over the transport. The response is received in
 * #HTTPResponse_t.pBuffer.
 *
 * If #HTTP_SEND_DISABLE_CONTENT_LENGTH_FLAG is not set in parameter @p sendFlags,
 * then the Content-Length to be sent to the server is automatically written to
 * @p pRequestHeaders. The Content-Length will not be written when there is
 * no request body. If there is not enough room in the buffer to write the
 * Content-Length then #HTTPInsufficientMemory is returned. Please see
 * #HTTP_MAX_CONTENT_LENGTH_HEADER_LENGTH for the maximum Content-Length header
 * field and value that could be written to the buffer.
 *
 * The application should close the connection with the server if any of the
 * following errors are returned:
 * - #HTTPSecurityAlertExtraneousResponseData
 * - #HTTPSecurityAlertInvalidChunkHeader
 * - #HTTPSecurityAlertInvalidProtocolVersion
 * - #HTTPSecurityAlertInvalidStatusCode
 * - #HTTPSecurityAlertInvalidCharacter
 * - #HTTPSecurityAlertInvalidContentLength
 *
 * The @p pResponse returned is valid only if this function returns HTTPSuccess.
 *
 * @param[in] pTransport Transport interface, see #TransportInterface_t for
 * more information.
 * @param[in] pRequestHeaders Request configuration containing the buffer of
 * headers to send.
 * @param[in] pRequestBodyBuf Optional Request entity body. Set to NULL if there
 * is no request body.
 * @param[in] reqBodyBufLen The length of the request entity in bytes.
 * @param[in] pResponse The response message and some notable response
 * parameters will be returned here on success.
 * @param[in] sendFlags Flags which modify the behavior of this function. Please
 * see @ref http_send_flags for more information.
 *
 * @return One of the following:
 * - #HTTPSuccess (If successful.)
 * - #HTTPInvalidParameter (If any provided parameters or their members are invalid.)
 * - #HTTPNetworkError (Errors in sending or receiving over the transport interface.)
 * - #HTTPPartialResponse (Part of an HTTP response was received in a partially filled response buffer.)
 * - #HTTPNoResponse (No data was received from the transport interface.)
 * - #HTTPInsufficientMemory (The response received could not fit into the response buffer
 * or extra headers could not be sent in the request.)
 * - #HTTPParserInternalError (Internal parsing error.)\n\n
 * Security alerts are listed below, please see #HTTPStatus_t for more information:
 * - #HTTPSecurityAlertExtraneousResponseData
 * - #HTTPSecurityAlertInvalidChunkHeader
 * - #HTTPSecurityAlertInvalidProtocolVersion
 * - #HTTPSecurityAlertInvalidStatusCode
 * - #HTTPSecurityAlertInvalidCharacter
 * - #HTTPSecurityAlertInvalidContentLength
 *
 * **Example**
 * @code{c}
 * // Variables used in this example.
 * HTTPStatus_t httpLibraryStatus = HTTPSuccess;
 * TransportInterface_t transportInterface = { 0 };
 * HTTPResponse_t = { 0 };
 * char requestBody[] = "This is an example request body.";
 *
 * // Assume that requestHeaders has been initialized with
 * // HTTPClient_InitializeResponseHeaders() and any additional headers have
 * // been added with HTTPClient_AddHeader().
 * HTTPRequestHeaders_t requestHeaders;
 *
 * // Set the transport interface with platform specific functions that are
 * // assumed to be implemented elsewhere.
 * transportInterface.recv = myPlatformTransportReceive;
 * transportInterface.send = myPlatformTransportSend;
 * transportInterface.pNetworkContext = myPlatformNetworkContext;
 *
 * // Set the buffer to receive the HTTP response message into. The buffer is
 * // dynamically allocated for demonstration purposes only.
 * response.pBuffer = ( uint8_t* )malloc( 1024 );
 * response.bufferLen = 1024;
 *
 * httpLibraryStatus = HTTPClient_Send( &transportInterface,
 *                                      &requestHeaders,
 *                                      requestBody,
 *                                      sizeof( requestBody ) - 1U,
 *                                      &response,
 *                                      0 );
 *
 * if( httpLibraryStatus == HTTPSuccess )
 * {
 *     if( response.status == 200 )
 *     {
 *         // Handle a response Status-Code of 200 OK.
 *     }
 * }
 * @endcode
 */
/* @[declare_httpclient_send] */
HTTPStatus_t HTTPClient_Send( const TransportInterface_t * pTransport,
                              HTTPRequestHeaders_t * pRequestHeaders,
                              const uint8_t * pRequestBodyBuf,
                              size_t reqBodyBufLen,
                              HTTPResponse_t * pResponse,
                              uint32_t sendFlags );
/* @[declare_httpclient_send] */

/**
 * @brief Receive the HTTP response from the network and parse it.
 *
 * @param[in] pTransport Transport interface, see #TransportInterface_t for more
 *  information.
 * @param[in] pResponse The response message and some notable response parameters will be
 * returned here on success.
 * @param[in] pRequestHeaders Request configuration containing the buffer of headers to
 * send.
 *
 * @return Returns #HTTPSuccess if successful. #HTTPNetworkError for a transport
 * receive error. Please see #parseHttpResponse and #getFinalResponseStatus for
 * other statuses returned.
 *
 */
/* @[declare_httpclient_receiveandparsehttpresponse] */
HTTPStatus_t HTTPClient_ReceiveAndParseHttpResponse( const TransportInterface_t * pTransport,
                                                     HTTPResponse_t * pResponse,
                                                     const HTTPRequestHeaders_t * pRequestHeaders );
/* @[declare_httpclient_receiveandparsehttpresponse] */

/**
 * @brief Read a header from a buffer containing a complete HTTP response.
 * This will return the location of the response header value in the
 * #HTTPResponse_t.pBuffer buffer.
 *
 * The location, within #HTTPResponse_t.pBuffer, of the value found, will be
 * returned in @p pValue. If the header value is empty for the found @p pField,
 * then this function will return #HTTPSuccess, and set the values for
 * @p pValueLoc and @p pValueLen as NULL and zero respectively. According to
 * RFC 2616, it is not invalid to have an empty value for some header fields.
 *
 * @note This function should only be called on a complete HTTP response. If the
 * request is sent through the #HTTPClient_Send function, the #HTTPResponse_t is
 * incomplete until #HTTPClient_Send returns.
 *
 * @param[in] pResponse The buffer containing the completed HTTP response.
 * @param[in] pField The header field name to read.
 * @param[in] fieldLen The length of the header field name in bytes.
 * @param[out] pValueLoc This will be populated with the location of the
 * header value in the response buffer, #HTTPResponse_t.pBuffer.
 * @param[out] pValueLen This will be populated with the length of the
 * header value in bytes.
 *
 * @return One of the following:
 * - #HTTPSuccess (If successful.)
 * - #HTTPInvalidParameter (If any provided parameters or their members are invalid.)
 * - #HTTPHeaderNotFound (Header is not found in the passed response buffer.)
 * - #HTTPInvalidResponse (Provided response is not a valid HTTP response for parsing.)
 * - #HTTPParserInternalError(If an error in the response parser.)
 *
 * **Example**
 * @code{c}
 * HTTPStatus_t httpLibraryStatus = HTTPSuccess;
 * // Assume that response is returned from a successful invocation of
 * // HTTPClient_Send().
 * HTTPResponse_t response;
 *
 * char * pDateLoc = NULL;
 * size_t dateLen = 0;
 * // Search for a "Date" header field. pDateLoc will be the location of the
 * // Date header value in response.pBuffer.
 * httpLibraryStatus = HTTPClient_ReadHeader( &response,
 *                                            "Date",
 *                                            sizeof("Date") - 1,
 *                                            &pDateLoc,
 *                                            &dateLen );
 * @endcode
 */
/* @[declare_httpclient_readheader] */
HTTPStatus_t HTTPClient_ReadHeader( const HTTPResponse_t * pResponse,
                                    const char * pField,
                                    size_t fieldLen,
                                    const char ** pValueLoc,
                                    size_t * pValueLen );
/* @[declare_httpclient_readheader] */

/**
 * @brief Error code to string conversion utility for HTTP Client library.
 *
 * @note This returns constant strings, which should not be modified.
 *
 * @param[in] status The status code to convert to a string.
 *
 * @return The string representation of the status code.
 */
/* @[declare_httpclient_strerror] */
const char * HTTPClient_strerror( HTTPStatus_t status );
/* @[declare_httpclient_strerror] */

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef CORE_HTTP_CLIENT_H_ */

// === source/include/core_http_client_private.h (verbatim from upstream) ===
/*
 * coreHTTP
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file core_http_client_private.h
 * @brief Internal definitions to the HTTP Client library.
 */

#ifndef CORE_HTTP_CLIENT_PRIVATE_H_
#define CORE_HTTP_CLIENT_PRIVATE_H_

/**
 * @cond DOXYGEN_IGNORE
 * http-parser defaults this to 1, llhttp to 0.
 */
#ifndef LLHTTP_STRICT_MODE
    #define LLHTTP_STRICT_MODE    0
#endif
/** @endcond */

/* Third-party llhttp include. */

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/**
 * @brief The HTTP protocol version of this library is HTTP/1.1.
 */
#define HTTP_PROTOCOL_VERSION              "HTTP/1.1"
#define HTTP_PROTOCOL_VERSION_LEN          ( sizeof( HTTP_PROTOCOL_VERSION ) - 1U ) /**< The length of #HTTP_PROTOCOL_VERSION. */

/**
 * @brief Default value when pRequestInfo->pPath == NULL.
 */
#define HTTP_EMPTY_PATH                    "/"
#define HTTP_EMPTY_PATH_LEN                ( sizeof( HTTP_EMPTY_PATH ) - 1U ) /**< The length of #HTTP_EMPTY_PATH. */

/* Constants for HTTP header formatting. */
#define HTTP_HEADER_LINE_SEPARATOR         "\r\n"                                         /**< HTTP header field lines are separated by `\r\n`. */
#define HTTP_HEADER_LINE_SEPARATOR_LEN     ( sizeof( HTTP_HEADER_LINE_SEPARATOR ) - 1U )  /**< The length of #HTTP_HEADER_LINE_SEPARATOR. */
#define HTTP_HEADER_END_INDICATOR          "\r\n\r\n"                                     /**< The HTTP header is complete when `\r\n\r\n` is found. */
#define HTTP_HEADER_END_INDICATOR_LEN      ( sizeof( HTTP_HEADER_END_INDICATOR ) - 1U )   /**< The length of #HTTP_HEADER_END_INDICATOR. */
#define HTTP_HEADER_FIELD_SEPARATOR        ": "                                           /**< HTTP header field and values are separated by ": ". */
#define HTTP_HEADER_FIELD_SEPARATOR_LEN    ( sizeof( HTTP_HEADER_FIELD_SEPARATOR ) - 1U ) /**< The length of #HTTP_HEADER_FIELD_SEPARATOR. */
#define SPACE_CHARACTER                    ' '                                            /**< A space character macro to help with serializing a request. */
#define SPACE_CHARACTER_LEN                ( 1U )                                         /**< The length of #SPACE_CHARACTER. */
#define DASH_CHARACTER                     '-'                                            /**< A dash character macro to help with serializing a request. */
#define DASH_CHARACTER_LEN                 ( 1U )                                         /**< The length of #DASH_CHARACTER. */

/* Constants for HTTP header copy checks. */
#define CARRIAGE_RETURN_CHARACTER          '\r' /**< A carriage return character to help with header validation. */
#define LINEFEED_CHARACTER                 '\n' /**< A linefeed character to help with header validation. */
#define COLON_CHARACTER                    ':'  /**< A colon character to help with header validation. */

/**
 * @brief Indicator for function #httpHeaderStrncpy that the pSrc parameter is a
 * header value.
 */
#define HTTP_HEADER_STRNCPY_IS_VALUE       0U

/**
 * @brief Indicator for function #httpHeaderStrncpy that the pSrc parameter is a
 * header field.
 */
#define HTTP_HEADER_STRNCPY_IS_FIELD       1U

/* Constants for header fields added automatically during the request
 * initialization. */
#define HTTP_USER_AGENT_FIELD              "User-Agent"                             /**< HTTP header field "User-Agent". */
#define HTTP_USER_AGENT_FIELD_LEN          ( sizeof( HTTP_USER_AGENT_FIELD ) - 1U ) /**< The length of #HTTP_USER_AGENT_FIELD. */
#define HTTP_HOST_FIELD                    "Host"                                   /**< HTTP header field "Host". */
#define HTTP_HOST_FIELD_LEN                ( sizeof( HTTP_HOST_FIELD ) - 1U )       /**< The length of #HTTP_HOST_FIELD. */
#define HTTP_USER_AGENT_VALUE_LEN          ( sizeof( HTTP_USER_AGENT_VALUE ) - 1U ) /**< The length of #HTTP_USER_AGENT_VALUE. */

/* Constants for header fields added based on flags. */
#define HTTP_CONNECTION_FIELD              "Connection"                                 /**< HTTP header field "Connection". */
#define HTTP_CONNECTION_FIELD_LEN          ( sizeof( HTTP_CONNECTION_FIELD ) - 1U )     /**< The length of #HTTP_CONNECTION_FIELD. */
#define HTTP_CONTENT_LENGTH_FIELD          "Content-Length"                             /**< HTTP header field "Content-Length". */
#define HTTP_CONTENT_LENGTH_FIELD_LEN      ( sizeof( HTTP_CONTENT_LENGTH_FIELD ) - 1U ) /**< The length of #HTTP_CONTENT_LENGTH_FIELD. */

/* Constants for header values added based on flags. */

/* MISRA Ref 5.4.1 [Macro identifiers] */
/* More details at: https://github.com/FreeRTOS/coreHTTP/blob/main/MISRA.md#rule-54 */
/* coverity[other_declaration] */
#define HTTP_CONNECTION_KEEP_ALIVE_VALUE    "keep-alive" /**< HTTP header value "keep-alive" for the "Connection" header field. */

/* MISRA Ref 5.4.2 [Macro identifiers] */
/* More details at: https://github.com/FreeRTOS/coreHTTP/blob/main/MISRA.md#rule-54 */
/* coverity[misra_c_2012_rule_5_4_violation] */
#define HTTP_CONNECTION_KEEP_ALIVE_VALUE_LEN    ( sizeof( HTTP_CONNECTION_KEEP_ALIVE_VALUE ) - 1U ) /**< The length of #HTTP_CONNECTION_KEEP_ALIVE_VALUE. */

/* Constants relating to Range Requests. */

/* MISRA Ref 5.4.3 [Macro identifiers] */
/* More details at: https://github.com/FreeRTOS/coreHTTP/blob/main/MISRA.md#rule-54 */
/* coverity[other_declaration] */
#define HTTP_RANGE_REQUEST_HEADER_FIELD    "Range" /**< HTTP header field "Range". */

/* MISRA Ref 5.4.4 [Macro identifiers] */
/* More details at: https://github.com/FreeRTOS/coreHTTP/blob/main/MISRA.md#rule-54 */
/* coverity[misra_c_2012_rule_5_4_violation] */
#define HTTP_RANGE_REQUEST_HEADER_FIELD_LEN    ( sizeof( HTTP_RANGE_REQUEST_HEADER_FIELD ) - 1U ) /**< The length of #HTTP_RANGE_REQUEST_HEADER_FIELD. */

/* MISRA Ref 5.4.5 [Macro identifiers] */
/* More details at: https://github.com/FreeRTOS/coreHTTP/blob/main/MISRA.md#rule-54 */
/* coverity[other_declaration] */
#define HTTP_RANGE_REQUEST_HEADER_VALUE_PREFIX    "bytes=" /**< HTTP required header value prefix when specifying a byte range for partial content. */

/* MISRA Ref 5.4.6 [Macro identifiers] */
/* More details at: https://github.com/FreeRTOS/coreHTTP/blob/main/MISRA.md#rule-54 */
/* coverity[misra_c_2012_rule_5_4_violation] */
#define HTTP_RANGE_REQUEST_HEADER_VALUE_PREFIX_LEN    ( sizeof( HTTP_RANGE_REQUEST_HEADER_VALUE_PREFIX ) - 1U ) /**< The length of #HTTP_RANGE_REQUEST_HEADER_VALUE_PREFIX. */

/**
 * @brief Maximum value of a 32 bit signed integer is 2,147,483,647.
 *
 * Used for calculating buffer space for ASCII representation of range values.
 */
#define MAX_INT32_NO_OF_DECIMAL_DIGITS                10U

/**
 * @brief Maximum buffer space for storing a Range Request Value.
 *
 * The largest Range Request value is of the form:
 * "bytes=<Max-Integer-Value>-<Max-Integer-Value>"
 */
#define HTTP_MAX_RANGE_REQUEST_VALUE_LEN                                            \
    ( HTTP_RANGE_REQUEST_HEADER_VALUE_PREFIX_LEN + MAX_INT32_NO_OF_DECIMAL_DIGITS + \
      1U /* Dash character '-' */ + MAX_INT32_NO_OF_DECIMAL_DIGITS )

/**
 * @brief Return value for llhttp registered callback to signal
 * continuation of HTTP response parsing. Equal to HPE_OK.
 */
#define LLHTTP_CONTINUE_PARSING             0

/**
 * @brief Return value for llhttp registered callback to signal halting
 * further execution.
 */
#define LLHTTP_STOP_PARSING                 HPE_USER

/**
 * @brief Return value for llhttp registered callback to signal to pause
 * further execution.
 */
#define LLHTTP_PAUSE_PARSING                HPE_PAUSED

/**
 * @brief Return value for llhttp_t.on_headers_complete to signal
 * that the HTTP response has no body and to halt further execution.
 */
#define LLHTTP_STOP_PARSING_NO_BODY         1

/**
 * @brief Return value for llhttp_t.on_headers_complete to signal
 * halting further execution. This is the same return value that
 * indicates the HTTP response has no body, but unlike the -1 error
 * code, gives consistent return values for llhttp_execute in both
 * strict and non-strict modes.
 */
#define LLHTTP_STOP_PARSING_NO_HEADER       1

/**
 * @brief The minimum request-line in the headers has a possible one character
 * custom method and a single forward / or asterisk * for the path:
 *
 * @code
 * <1 character custom method> <1 character / or *> HTTP/1.x\r\n\r\n
 * @endcode
 *
 * Therefore the minimum length is 16. If this minimum request-line is not
 * satisfied, then the request headers to send are invalid.
 *
 * Note that custom methods are allowed per:
 * https://tools.ietf.org/html/rfc2616#section-5.1.1.
 */
#define HTTP_MINIMUM_REQUEST_LINE_LENGTH    16u

/**
 * @brief The state of the response message parsed after function
 * #parseHttpResponse returns.
 */
typedef enum HTTPParsingState
{
    HTTP_PARSING_NONE = 0,   /**< The parser has not started reading any response. */
    HTTP_PARSING_INCOMPLETE, /**< The parser found a partial response. */
    HTTP_PARSING_COMPLETE    /**< The parser found the entire response. */
} HTTPParsingState_t;

/**
 * @brief An aggregator that represents the user-provided parameters to the
 * #HTTPClient_ReadHeader API function. This will be used as context parameter
 * for the parsing callbacks used by the API function.
 */
typedef struct findHeaderContext
{
    const char * pField;     /**< The field that is being searched for. */
    size_t fieldLen;         /**< The length of pField. */
    const char ** pValueLoc; /**< The location of the value found in the buffer. */
    size_t * pValueLen;      /**< the length of the value found. */
    uint8_t fieldFound;      /**< Indicates that the header field was found during parsing. */
    uint8_t valueFound;      /**< Indicates that the header value was found during parsing. */
} findHeaderContext_t;

/**
 * @brief The HTTP response parsing context for a response fresh from the
 * server. This context is passed into the http-parser registered callbacks.
 * The registered callbacks are private functions of the form
 * httpParserXXXXCallbacks().
 *
 * The transitions of the httpParserXXXXCallback() functions are shown below.
 * The  XXXX is replaced by the strings in the state boxes:
 *
 * +---------------------+
 * |onMessageBegin       |
 * +--------+------------+
 *          |
 *          |
 *          |
 *          v
 * +--------+------------+
 * |onStatus             |
 * +--------+------------+
 *          |
 *          |
 *          |
 *          v
 * +--------+------------+
 * |onStatusComplete     |
 * +--------+------------+
 *          |
 *          |
 *          |
 *          v
 * +--------+------------+
 * |onHeaderField        +<---+
 * +--------+------------+    |
 *          |                 |
 *          |                 |(More headers)
 *          |                 |
 *          v                 |
 * +--------+------------+    |
 * |onHeaderValue        +----^
 * +--------+------------+
 *          |
 *          |
 *          |
 *          v
 * +--------+------------+
 * |onHeadersComplete    |
 * +---------------------+
 *          |
 *          |
 *          |
 *          v
 * +--------+------------+
 * |onBody               +<---+
 * +--------+--------+---+    |
 *          |        |        |(Transfer-encoding chunked body)
 *          |        |        |
 *          |        +--------+
 *          |
 *          v
 * +--------+------------+
 * |onMessageComplete    |
 * +---------------------+
 */
typedef struct HTTPParsingContext
{
    llhttp_t llhttpParser;            /**< Third-party llhttp context. */
    llhttp_settings_t llhttpSettings; /**< Third-party parser settings. */
    HTTPParsingState_t state;         /**< The current state of the HTTP response parsed. */
    HTTPResponse_t * pResponse;       /**< HTTP response associated with this parsing context. */
    uint8_t isHeadResponse;           /**< HTTP response is for a HEAD request. */

    const char * pBufferCur;          /**< The current location of the parser in the response buffer. */
    const char * pLastHeaderField;    /**< Holds the last part of the header field parsed. */
    size_t lastHeaderFieldLen;        /**< The length of the last header field parsed. */
    const char * pLastHeaderValue;    /**< Holds the last part of the header value parsed. */
    size_t lastHeaderValueLen;        /**< The length of the last value field parsed. */
} HTTPParsingContext_t;

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef CORE_HTTP_CLIENT_PRIVATE_H_ */

// === source/include/core_http_config_defaults.h (verbatim from upstream) ===
/*
 * coreHTTP
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file core_http_config_defaults.h
 * @brief The default values for the configuration macros for the HTTP Client
 * library.
 *
 * @note This file SHOULD NOT be modified. If custom values are needed for
 * any configuration macro, a core_http_config.h file should be provided to
 * the HTTP Client library to override the default values defined in this file.
 * To use the custom config file, the HTTP_DO_NOT_USE_CUSTOM_CONFIG preprocessor
 * macro SHOULD NOT be set.
 */

#ifndef CORE_HTTP_CONFIG_DEFAULTS_
#define CORE_HTTP_CONFIG_DEFAULTS_

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/**
 * @brief The HTTP header "User-Agent" value.
 *
 * The following header line is automatically written to
 * #HTTPRequestHeaders_t.pBuffer:
 * "User-Agent: my-platform-name\r\n"
 *
 * <b>Possible values:</b> Any string. <br>
 * <b>Default value:</b> `my-platform-name`
 */
#ifndef HTTP_USER_AGENT_VALUE
    #define HTTP_USER_AGENT_VALUE    "my-platform-name"
#endif

/**
 * @brief The maximum duration between non-empty network reads while receiving
 * an HTTP response via the #HTTPClient_ReceiveAndParseHttpResponse API function.
 *
 * The transport receive function may be called multiple times until the end of
 * the response is detected by the parser. This timeout represents the maximum
 * duration that is allowed without any data reception from the network for the
 * incoming response.
 *
 * If the timeout expires, the #HTTPClient_ReceiveAndParseHttpResponse function will return
 * #HTTPNetworkError.
 *
 * If #HTTPResponse_t.getTime is set to NULL, then this HTTP_RECV_RETRY_TIMEOUT_MS
 * is unused. When this timeout is unused, #HTTPClient_ReceiveAndParseHttpResponse will not retry the
 * transport receive calls that return zero bytes read.
 *
 * <b>Possible values:</b> Any positive 32 bit integer. A small timeout value
 * is recommended. <br>
 * <b>Default value:</b> `10`
 */
#ifndef HTTP_RECV_RETRY_TIMEOUT_MS
    #define HTTP_RECV_RETRY_TIMEOUT_MS    ( 10U )
#endif

/**
 * @brief The maximum duration between non-empty network transmissions while
 * sending an HTTP request via the #HTTPClient_Send API function.
 *
 * When sending an HTTP request, the transport send function may be called multiple
 * times until all of the required number of bytes are sent.
 * This timeout represents the maximum duration that is allowed for no data
 * transmission over the network through the transport send function.
 *
 * If the timeout expires, the #HTTPClient_Send function returns #HTTPNetworkError.
 *
 * If #HTTPResponse_t.getTime is set to NULL, then this HTTP_RECV_RETRY_TIMEOUT_MS
 * is unused. When this timeout is unused, #HTTPClient_Send will not retry the
 * transport send calls that return zero bytes sent.
 *
 * <b>Possible values:</b> Any positive 32 bit integer. A small timeout value
 * is recommended. <br>
 * <b>Default value:</b> `10`
 */
#ifndef HTTP_SEND_RETRY_TIMEOUT_MS
    #define HTTP_SEND_RETRY_TIMEOUT_MS    ( 10U )
#endif

/**
 * @brief Macro that is called in the HTTP Client library for logging "Error" level
 * messages.
 *
 * To enable error level logging in the HTTP Client library, this macro should be mapped to the
 * application-specific logging implementation that supports error logging.
 *
 * @note This logging macro is called in the HTTP Client library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_http_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C).
 *
 * <b>Default value</b>: Error logging is turned off, and no code is generated for calls
 * to the macro in the HTTP Client library on compilation.
 */
#ifndef LogError
    #define LogError( message )
#endif

/**
 * @brief Macro that is called in the HTTP Client library for logging "Warning" level
 * messages.
 *
 * To enable warning level logging in the HTTP Client library, this macro should be mapped to the
 * application-specific logging implementation that supports warning logging.
 *
 * @note This logging macro is called in the HTTP Client library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_http_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C).
 *
 * <b>Default value</b>: Warning logs are turned off, and no code is generated for calls
 * to the macro in the HTTP Client library on compilation.
 */
#ifndef LogWarn
    #define LogWarn( message )
#endif

/**
 * @brief Macro that is called in the HTTP Client library for logging "Info" level
 * messages.
 *
 * To enable info level logging in the HTTP Client library, this macro should be mapped to the
 * application-specific logging implementation that supports info logging.
 *
 * @note This logging macro is called in the HTTP Client library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_http_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C).
 *
 * <b>Default value</b>: Info logging is turned off, and no code is generated for calls
 * to the macro in the HTTP Client library on compilation.
 */
#ifndef LogInfo
    #define LogInfo( message )
#endif

/**
 * @brief Macro that is called in the HTTP Client library for logging "Debug" level
 * messages.
 *
 * To enable debug level logging from HTTP Client library, this macro should be mapped to the
 * application-specific logging implementation that supports debug logging.
 *
 * @note This logging macro is called in the HTTP Client library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_http_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C).
 *
 * <b>Default value</b>: Debug logging is turned off, and no code is generated for calls
 * to the macro in the HTTP Client library on compilation.
 */
#ifndef LogDebug
    #define LogDebug( message )
#endif

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef CORE_HTTP_CONFIG_DEFAULTS_ */

// === source/core_http_client.c (verbatim from upstream) ===
/*
 * coreHTTP
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file core_http_client.c
 * @brief Implements the user-facing functions in core_http_client.h.
 */
#include <assert.h>
#include <string.h>
#include <ctype.h>


/*-----------------------------------------------------------*/

/**
 * @brief When #HTTPResponse_t.getTime is set to NULL in #HTTPClient_Send then
 * this function will replace that field.
 *
 * @return This function always returns zero.
 */
static uint32_t getZeroTimestampMs( void );

/**
 * @brief Adds the Content-Length header field and value to the
 * @p pRequestHeaders.
 *
 * @param[in] pRequestHeaders Request header buffer information.
 * @param[in] contentLength The Content-Length header value to write.
 *
 * @return #HTTPSuccess if successful. If there was insufficient memory in the
 * application buffer, then #HTTPInsufficientMemory is returned.
 */
static HTTPStatus_t addContentLengthHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                            size_t contentLength );

/**
 * @brief Send the HTTP body over the transport send interface.
 *
 * @param[in] pTransport Transport interface.
 * @param[in] getTimestampMs Function to retrieve a timestamp in milliseconds.
 * @param[in] pRequestBodyBuf Request body buffer.
 * @param[in] reqBodyBufLen Length of the request body buffer.
 *
 * @return #HTTPSuccess if successful. If there was a network error or less
 * bytes than what was specified were sent, then #HTTPNetworkError is
 * returned.
 */
static HTTPStatus_t sendHttpBody( const TransportInterface_t * pTransport,
                                  HTTPClient_GetCurrentTimeFunc_t getTimestampMs,
                                  const uint8_t * pRequestBodyBuf,
                                  size_t reqBodyBufLen );

/**
 * @brief A strncpy replacement with HTTP header validation.
 *
 * This function checks for `\r` and `\n` in the @p pSrc while copying.
 * This function checks for `:` in the @p pSrc, if @p isField is set to 1.
 *
 * @param[in] pDest The destination buffer to copy to.
 * @param[in] pSrc The source buffer to copy from.
 * @param[in] len The length of @p pSrc to copy to pDest.
 * @param[in] isField Set to 0 to indicate that @p pSrc is a field. Set to 1 to
 * indicate that @p pSrc is a value.
 *
 * @return @p pDest if the copy was successful, NULL otherwise.
 */
static char * httpHeaderStrncpy( char * pDest,
                                 const char * pSrc,
                                 size_t len,
                                 uint8_t isField );

/**
 * @brief Write header based on parameters. This method also adds a trailing
 * "\r\n". If a trailing "\r\n" already exists in the HTTP header, this method
 * backtracks in order to write over it and updates the length accordingly.
 *
 * @param[in] pRequestHeaders Request header buffer information.
 * @param[in] pField The ISO 8859-1 encoded header field name to write.
 * @param[in] fieldLen The byte length of the header field name.
 * @param[in] pValue The ISO 8859-1 encoded header value to write.
 * @param[in] valueLen The byte length of the header field value.
 *
 * @return #HTTPSuccess if successful. If there was insufficient memory in the
 * application buffer, then #HTTPInsufficientMemory is returned.
 */
static HTTPStatus_t addHeader( HTTPRequestHeaders_t * pRequestHeaders,
                               const char * pField,
                               size_t fieldLen,
                               const char * pValue,
                               size_t valueLen );

/**
 * @brief Add the byte range request header to the request headers store in
 * #HTTPRequestHeaders_t.pBuffer once all the parameters are validated.
 *
 * @param[in] pRequestHeaders Request header buffer information.
 * @param[in] rangeStartOrlastNbytes Represents either the starting byte
 * for a range OR the last N number of bytes in the requested file.
 * @param[in] rangeEnd The ending range for the requested file. For end of file
 * byte in Range Specifications 2. and 3., #HTTP_RANGE_REQUEST_END_OF_FILE
 * should be passed.
 *
 * @return #HTTPSuccess if successful. If there was insufficient memory in the
 * application buffer, then #HTTPInsufficientMemory is returned.
 */
static HTTPStatus_t addRangeHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                    int32_t rangeStartOrlastNbytes,
                                    int32_t rangeEnd );

/**
 * @brief Get the status of the HTTP response given the parsing state and how
 * much data is in the response buffer.
 *
 * @param[in] parsingState State of the parsing on the HTTP response.
 * @param[in] totalReceived The amount of network data received in the response
 * buffer.
 * @param[in] pResponse  The response information.
 *
 * @return Returns #HTTPSuccess if the parsing state is complete. If
 * the parsing state denotes it never started, then return #HTTPNoResponse. If
 * the parsing state is incomplete, then if the response buffer is not full
 * #HTTPPartialResponse is returned. If the parsing state is incomplete, then
 * if the response buffer is full #HTTPInsufficientMemory is returned.
 */
static HTTPStatus_t getFinalResponseStatus( HTTPParsingState_t parsingState,
                                            size_t totalReceived,
                                            const HTTPResponse_t * pResponse );

/**
 * @brief Send the HTTP request over the network.
 *
 * @param[in] pTransport Transport interface.
 * @param[in] getTimestampMs Function to retrieve a timestamp in milliseconds.
 * @param[in] pRequestHeaders Request headers to send over the network.
 * @param[in] pRequestBodyBuf Request body buffer to send over the network.
 * @param[in] reqBodyBufLen Length of the request body buffer.
 * @param[in] sendFlags Application provided flags to #HTTPClient_Send.
 *
 * @return Returns #HTTPSuccess if successful. Please see #HTTPClient_SendHttpHeaders and
 * #sendHttpBody for other statuses returned.
 */
static HTTPStatus_t sendHttpRequest( const TransportInterface_t * pTransport,
                                     HTTPClient_GetCurrentTimeFunc_t getTimestampMs,
                                     HTTPRequestHeaders_t * pRequestHeaders,
                                     const uint8_t * pRequestBodyBuf,
                                     size_t reqBodyBufLen,
                                     uint32_t sendFlags );

/**
 * @brief Converts an integer value to its ASCII representation in the passed
 * buffer.
 *
 * @param[in] value The value to convert to ASCII.
 * @param[out] pBuffer The buffer to store the ASCII representation of the
 * integer.
 * @param[in] bufferLength The length of pBuffer.
 *
 * @return Returns the number of bytes written to @p pBuffer.
 */
static uint8_t convertInt32ToAscii( int32_t value,
                                    char * pBuffer,
                                    size_t bufferLength );

/**
 * @brief This method writes the request line (first line) of the HTTP Header
 * into #HTTPRequestHeaders_t.pBuffer and updates length accordingly.
 *
 * @param pRequestHeaders Request header buffer information.
 * @param pMethod The HTTP request method e.g. "GET", "POST", "PUT", or "HEAD".
 * @param methodLen The byte length of the request method.
 * @param pPath The Request-URI to the objects of interest, e.g. "/path/to/item.txt".
 * @param pathLen The byte length of the request path.
 *
 * @return #HTTPSuccess if successful. If there was insufficient memory in the
 * application buffer, then #HTTPInsufficientMemory is returned.
 */
static HTTPStatus_t writeRequestLine( HTTPRequestHeaders_t * pRequestHeaders,
                                      const char * pMethod,
                                      size_t methodLen,
                                      const char * pPath,
                                      size_t pathLen );

/**
 * @brief Find the specified header field in the response buffer.
 *
 * @param[in] pBuffer The response buffer to parse.
 * @param[in] bufferLen The length of the response buffer to parse.
 * @param[in] pField The header field to search for.
 * @param[in] fieldLen The length of pField.
 * @param[out] pValueLoc The location of the the header value found in pBuffer.
 * @param[out] pValueLen The length of pValue.
 *
 * @return One of the following:
 * - #HTTPSuccess when header is found in the response.
 * - #HTTPHeaderNotFound if requested header is not found in response.
 * - #HTTPInvalidResponse if passed response is invalid for parsing.
 * - #HTTPParserInternalError for any parsing errors.
 */
static HTTPStatus_t findHeaderInResponse( const uint8_t * pBuffer,
                                          size_t bufferLen,
                                          const char * pField,
                                          size_t fieldLen,
                                          const char ** pValueLoc,
                                          size_t * pValueLen );

/**
 * @brief The "on_header_field" callback for the HTTP parser used by the
 * #findHeaderInResponse function. The callback checks whether the parser
 * header field matched the header being searched for, and sets a flag to
 * represent reception of the header accordingly.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 * @param[in] pFieldLoc The location of the parsed header field in the response
 * buffer.
 * @param[in] fieldLen The length of the header field.
 *
 * @return Returns #LLHTTP_CONTINUE_PARSING to indicate continuation with
 * parsing.
 */
static int findHeaderFieldParserCallback( llhttp_t * pHttpParser,
                                          const char * pFieldLoc,
                                          size_t fieldLen );

/**
 * @brief The "on_header_value" callback for the HTTP parser used by the
 * #findHeaderInResponse function. The callback sets the user-provided output
 * parameters for header value if the requested header's field was found in the
 * @ref findHeaderFieldParserCallback function.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 * @param[in] pValueLoc The location of the parsed header value in the response
 * buffer.
 * @param[in] valueLen The length of the header value.
 *
 * @return Returns #LLHTTP_STOP_PARSING, if the header field/value pair are
 * found, otherwise #LLHTTP_CONTINUE_PARSING is returned.
 */
static int findHeaderValueParserCallback( llhttp_t * pHttpParser,
                                          const char * pValueLoc,
                                          size_t valueLen );

/**
 * @brief The "on_header_complete" callback for the HTTP parser used by the
 * #findHeaderInResponse function.
 *
 * This callback will only be invoked if the requested header is not found in
 * the response. This callback is used to signal the parser to halt execution
 * if the requested header is not found.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 *
 * @return Returns #LLHTTP_STOP_PARSING_NO_HEADER for the parser to halt further
 * execution, as all headers have been parsed in the response.
 */
static int findHeaderOnHeaderCompleteCallback( llhttp_t * pHttpParser );


/**
 * @brief Initialize the parsing context for parsing a response fresh from the
 * server.
 *
 * @param[in] pParsingContext The parsing context to initialize.
 * @param[in] pRequestHeaders Request headers for the corresponding HTTP request.
 */
static void initializeParsingContextForFirstResponse( HTTPParsingContext_t * pParsingContext,
                                                      const HTTPRequestHeaders_t * pRequestHeaders );

/**
 * @brief Parses the response buffer in @p pResponse.
 *
 * This function may be invoked multiple times for different parts of the the
 * HTTP response. The state of what was last parsed in the response is kept in
 * @p pParsingContext.
 *
 * @param[in,out] pParsingContext The response parsing state.
 * @param[in,out] pResponse The response information to be updated.
 * @param[in] parseLen The next length to parse in pResponse->pBuffer.
 *
 * @return One of the following:
 * - #HTTPSuccess
 * - #HTTPInvalidParameter
 * - Please see #processLlhttpError for parsing errors returned.
 */
static HTTPStatus_t parseHttpResponse( HTTPParsingContext_t * pParsingContext,
                                       HTTPResponse_t * pResponse,
                                       size_t parseLen );

/**
 * @brief Callback invoked during llhttp_execute() to indicate the start of
 * the HTTP response message.
 *
 * This callback is invoked when an "H" in the "HTTP/1.1" that starts a response
 * is found.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 *
 * @return #LLHTTP_CONTINUE_PARSING to continue parsing.
 */
static int httpParserOnMessageBeginCallback( llhttp_t * pHttpParser );

/**
 * @brief Callback invoked during llhttp_execute() when the HTTP response
 * status-code and its associated reason-phrase are found.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 * @param[in] pLoc Location of the HTTP response reason-phrase string in the
 * response message buffer.
 * @param[in] length Length of the HTTP response status code string.
 *
 * @return #LLHTTP_CONTINUE_PARSING to continue parsing.
 */
static int httpParserOnStatusCallback( llhttp_t * pHttpParser,
                                       const char * pLoc,
                                       size_t length );

/**
 * @brief Callback invoked during llhttp_execute() when the HTTP response
 * status parsing is complete.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 *
 * @return #LLHTTP_CONTINUE_PARSING to continue parsing.
 */
static int httpParserOnStatusCompleteCallback( llhttp_t * pHttpParser );

/**
 * @brief Callback invoked during llhttp_execute() when an HTTP response
 * header field is found.
 *
 * If only part of the header field was found, then parsing of the next part of
 * the response message will invoke this callback in succession.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 * @param[in] pLoc Location of the header field string in the response
 * message buffer.
 * @param[in] length Length of the header field.
 *
 * @return #LLHTTP_CONTINUE_PARSING to continue parsing.
 */
static int httpParserOnHeaderFieldCallback( llhttp_t * pHttpParser,
                                            const char * pLoc,
                                            size_t length );

/**
 * @brief Callback invoked during llhttp_execute() when an HTTP response
 * header value is found.
 *
 * This header value corresponds to the header field that was found in the
 * immediately preceding httpParserOnHeaderFieldCallback().
 *
 * If only part of the header value was found, then parsing of the next part of
 * the response message will invoke this callback in succession.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 * @param[in] pLoc Location of the header value in the response message buffer.
 * @param[in] length Length of the header value.
 *
 * @return #LLHTTP_CONTINUE_PARSING to continue parsing.
 */
static int httpParserOnHeaderValueCallback( llhttp_t * pHttpParser,
                                            const char * pLoc,
                                            size_t length );

/**
 * @brief Callback invoked during llhttp_execute() when the end of the
 * headers are found.
 *
 * The end of the headers is signaled in a HTTP response message by another
 * "\r\n" after the final header line.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 *
 * @return #LLHTTP_CONTINUE_PARSING to continue parsing.
 * #LLHTTP_STOP_PARSING_NO_BODY is returned if the response is for a HEAD request.
 */
static int httpParserOnHeadersCompleteCallback( llhttp_t * pHttpParser );

/**
 * @brief Callback invoked during llhttp_execute() when the HTTP response
 * body is found.
 *
 * If only part of the response body was found, then parsing of the next part of
 * the response message will invoke this callback in succession.
 *
 * This callback will be also invoked in succession if the response body is of
 * type "Transfer-Encoding: chunked". This callback will be invoked after each
 * chunk header.
 *
 * The follow is an example of a Transfer-Encoding chunked response:
 *
 * @code
 * HTTP/1.1 200 OK\r\n
 * Content-Type: text/plain\r\n
 * Transfer-Encoding: chunked\r\n
 * \r\n
 * d\r\n
 * Hello World! \r\n
 * 7\r\n
 * I am a \r\n
 * a\r\n
 * developer.\r\n
 * 0\r\n
 * \r\n
 * @endcode
 *
 * The first invocation of this callback will contain @p pLoc = "Hello World!"
 * and @p length = 13.
 * The second invocation of this callback will contain @p pLoc = "I am a " and
 * @p length = 7.
 * The third invocation of this callback will contain @p pLoc = "developer." and
 * @p length = 10.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 * @param[in] pLoc - Pointer to the body string in the response message buffer.
 * @param[in] length - The length of the body found.
 *
 * @return Zero to continue parsing. All other return values will stop parsing
 * and llhttp_execute() will return with the same value.
 */
static int httpParserOnBodyCallback( llhttp_t * pHttpParser,
                                     const char * pLoc,
                                     size_t length );

/**
 * @brief Callback invoked during llhttp_execute() to indicate the the
 * completion of an HTTP response message.
 *
 * When there is no response body, the end of the response message is when the
 * headers end. This is indicated by another "\r\n" after the final header line.
 *
 * When there is response body, the end of the response message is when the
 * full "Content-Length" value is parsed following the end of the headers. If
 * there is no Content-Length header, then llhttp_execute() expects a
 * zero length-ed parsing data to indicate the end of the response.
 *
 * For a "Transfer-Encoding: chunked" type of response message, the complete
 * response message is signaled by a terminating chunk header with length zero.
 *
 * See https://github.com/nodejs/llhttp for more information.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 *
 * @return Zero to continue parsing. All other return values will stop parsing
 * and llhttp_execute() will return with the same value.
 */
static int httpParserOnMessageCompleteCallback( llhttp_t * pHttpParser );

/**
 * @brief When a complete header is found the HTTP response header count
 * increases and the application is notified.
 *
 * This function is invoked only in callbacks that could follow
 * #httpParserOnHeaderValueCallback. These callbacks are
 * #httpParserOnHeaderFieldCallback and #httpParserOnHeadersCompleteCallback.
 * A header field and value is not is not known to be complete until
 * #httpParserOnHeaderValueCallback is not called in succession.
 *
 * @param[in] pParsingContext Parsing state containing information to notify
 * the application of a complete header.
 */
static void processCompleteHeader( HTTPParsingContext_t * pParsingContext );

/**
 * @brief When parsing is complete an error could be indicated in
 * pHttpParser->error. This function translates that error into a library
 * specific error code.
 *
 * @param[in] pHttpParser Third-party HTTP parsing context.
 *
 * @return One of the following:
 * - #HTTPSuccess
 * - #HTTPSecurityAlertExtraneousResponseData
 * - #HTTPSecurityAlertInvalidChunkHeader
 * - #HTTPSecurityAlertInvalidProtocolVersion
 * - #HTTPSecurityAlertInvalidStatusCode
 * - #HTTPSecurityAlertInvalidCharacter
 * - #HTTPSecurityAlertInvalidContentLength
 * - #HTTPParserInternalError
 */
static HTTPStatus_t processLlhttpError( const llhttp_t * pHttpParser );

/**
 * @brief Compares at most the first n bytes of str1 and str2 without case sensitivity
 * and n must be less than the actual size of either string.
 *
 * @param[in] str1 First string to be compared.
 * @param[in] str2 Second string to be compared.
 * @param[in] n The maximum number of characters to be compared.
 *
 * @return One of the following:
 * 0 if str1 is equal to str2
 * 1 if str1 is not equal to str2.
 */
static int8_t caseInsensitiveStringCmp( const char * str1,
                                        const char * str2,
                                        size_t n );

/*-----------------------------------------------------------*/

static uint32_t getZeroTimestampMs( void )
{
    return 0U;
}

/*-----------------------------------------------------------*/
static int8_t caseInsensitiveStringCmp( const char * str1,
                                        const char * str2,
                                        size_t n )
{
    size_t i = 0U;
    /* Inclusion of temporary variables for MISRA rule 13.2 compliance */
    char firstChar;
    char secondChar;
    /* Get the offset from a lowercase to capital character in a MISRA compliant way */
    int8_t offset = 'a' - 'A';

    for( i = 0U; i < n; i++ )
    {
        firstChar = str1[ i ];
        secondChar = str2[ i ];

        /* Subtract offset to go from lowercase to uppercase ASCII character */
        if( ( firstChar >= 'a' ) && ( firstChar <= 'z' ) )
        {
            firstChar = ( char ) ( firstChar - offset );
        }

        if( ( secondChar >= 'a' ) && ( secondChar <= 'z' ) )
        {
            secondChar = ( char ) ( secondChar - offset );
        }

        if( ( firstChar ) != ( secondChar ) )
        {
            break;
        }
    }

    return ( i == n ) ? 0 : 1;
}


/*-----------------------------------------------------------*/

static void processCompleteHeader( HTTPParsingContext_t * pParsingContext )
{
    HTTPResponse_t * pResponse = NULL;

    assert( pParsingContext != NULL );
    assert( pParsingContext->pResponse != NULL );

    pResponse = pParsingContext->pResponse;

    /* A header is complete when both the last header field and value have been
     * filled in. */
    if( ( pParsingContext->pLastHeaderField != NULL ) &&
        ( pParsingContext->pLastHeaderValue != NULL ) )
    {
        assert( pResponse->headerCount < SIZE_MAX );
        /* Increase the header count. */
        pResponse->headerCount++;

        LogDebug( ( "Response parsing: Found complete header: "
                    "HeaderField=%.*s, HeaderValue=%.*s",
                    ( int ) ( pParsingContext->lastHeaderFieldLen ),
                    pParsingContext->pLastHeaderField,
                    ( int ) ( pParsingContext->lastHeaderValueLen ),
                    pParsingContext->pLastHeaderValue ) );

        /* If the application registered a callback, then it must be notified. */
        if( pResponse->pHeaderParsingCallback != NULL )
        {
            pResponse->pHeaderParsingCallback->onHeaderCallback(
                pResponse->pHeaderParsingCallback->pContext,
                pParsingContext->pLastHeaderField,
                pParsingContext->lastHeaderFieldLen,
                pParsingContext->pLastHeaderValue,
                pParsingContext->lastHeaderValueLen,
                pResponse->statusCode );
        }

        /* Prepare the next header field and value for the first invocation of
         * httpParserOnHeaderFieldCallback() and
         * httpParserOnHeaderValueCallback(). */
        pParsingContext->pLastHeaderField = NULL;
        pParsingContext->lastHeaderFieldLen = 0U;
        pParsingContext->pLastHeaderValue = NULL;
        pParsingContext->lastHeaderValueLen = 0U;
    }
}

/*-----------------------------------------------------------*/

static int httpParserOnMessageBeginCallback( llhttp_t * pHttpParser )
{
    HTTPParsingContext_t * pParsingContext = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );

    pParsingContext = ( HTTPParsingContext_t * ) ( pHttpParser->data );

    /* Parsing has initiated. */
    pParsingContext->state = HTTP_PARSING_INCOMPLETE;

    LogDebug( ( "Response parsing: Found the start of the response message." ) );

    return LLHTTP_CONTINUE_PARSING;
}

/*-----------------------------------------------------------*/

static int httpParserOnStatusCallback( llhttp_t * pHttpParser,
                                       const char * pLoc,
                                       size_t length )
{
    HTTPParsingContext_t * pParsingContext = NULL;
    HTTPResponse_t * pResponse = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );
    assert( pLoc != NULL );

    pParsingContext = ( HTTPParsingContext_t * ) ( pHttpParser->data );
    pResponse = pParsingContext->pResponse;

    assert( pResponse != NULL );

    /* Set the location of what to parse next. */
    pParsingContext->pBufferCur = &pLoc[ length ];

    /* Initialize the first header field and value to be passed to the user
     * callback. */
    pParsingContext->pLastHeaderField = NULL;
    pParsingContext->lastHeaderFieldLen = 0U;
    pParsingContext->pLastHeaderValue = NULL;
    pParsingContext->lastHeaderValueLen = 0U;

    /* httpParserOnStatusCallback() is reached because llhttp_execute() has
     * successfully read the HTTP response status code. */
    pResponse->statusCode = ( uint16_t ) ( pHttpParser->status_code );

    LogDebug( ( "Response parsing: Found the Reason-Phrase: "
                "StatusCode=%u, ReasonPhrase=%.*s",
                ( unsigned int ) pResponse->statusCode,
                ( int ) length,
                pLoc ) );

    return LLHTTP_CONTINUE_PARSING;
}

/*-----------------------------------------------------------*/

static int httpParserOnStatusCompleteCallback( llhttp_t * pHttpParser )
{
    HTTPParsingContext_t * pParsingContext = NULL;
    HTTPResponse_t * pResponse = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );

    pParsingContext = ( HTTPParsingContext_t * ) ( pHttpParser->data );
    pResponse = pParsingContext->pResponse;

    assert( pResponse != NULL );

    /* Initialize the first header field and value to be passed to the user
     * callback. */
    pParsingContext->pLastHeaderField = NULL;
    pParsingContext->lastHeaderFieldLen = 0U;
    pParsingContext->pLastHeaderValue = NULL;
    pParsingContext->lastHeaderValueLen = 0U;

    /* httpParserOnStatusCompleteCallback() is reached because llhttp_execute()
     * has successfully read the HTTP response status code. */
    pResponse->statusCode = ( uint16_t ) ( pHttpParser->status_code );

    LogDebug( ( "Response parsing: StatusCode=%u",
                ( unsigned int ) pResponse->statusCode ) );

    return LLHTTP_CONTINUE_PARSING;
}

/*-----------------------------------------------------------*/

static int httpParserOnHeaderFieldCallback( llhttp_t * pHttpParser,
                                            const char * pLoc,
                                            size_t length )
{
    HTTPParsingContext_t * pParsingContext = NULL;
    HTTPResponse_t * pResponse = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );
    assert( pLoc != NULL );

    if( length == 0U )
    {
        LogError( ( "Received zero-length header field name from parser." ) );
        return LLHTTP_STOP_PARSING;
    }

    pParsingContext = ( HTTPParsingContext_t * ) ( pHttpParser->data );
    pResponse = pParsingContext->pResponse;

    assert( pResponse != NULL );

    /* If this is the first time httpParserOnHeaderFieldCallback() has been
     * invoked on a response, then the start of the response headers is NULL. */
    if( pResponse->pHeaders == NULL )
    {
        pResponse->pHeaders = ( const uint8_t * ) pLoc;
    }

    /* Set the location of what to parse next. */
    pParsingContext->pBufferCur = &pLoc[ length ];

    /* The httpParserOnHeaderFieldCallback() always follows the
     * httpParserOnHeaderValueCallback() if there is another header field. When
     * httpParserOnHeaderValueCallback() is not called in succession, then a
     * complete header has been found. */
    processCompleteHeader( pParsingContext );

    /* If httpParserOnHeaderFieldCallback() is invoked in succession, then the
     * last time llhttp_execute() was called only part of the header field
     * was parsed. The indication of successive invocations is a non-NULL
     * pParsingContext->pLastHeaderField. */
    if( pParsingContext->pLastHeaderField == NULL )
    {
        pParsingContext->pLastHeaderField = pLoc;
        pParsingContext->lastHeaderFieldLen = length;
    }
    else
    {
        assert( pParsingContext->lastHeaderFieldLen <= SIZE_MAX - length );
        pParsingContext->lastHeaderFieldLen += length;
    }

    LogDebug( ( "Response parsing: Found a header field: "
                "HeaderField=%.*s",
                ( int ) length,
                pLoc ) );

    return LLHTTP_CONTINUE_PARSING;
}

/*-----------------------------------------------------------*/

static int httpParserOnHeaderValueCallback( llhttp_t * pHttpParser,
                                            const char * pLoc,
                                            size_t length )
{
    HTTPParsingContext_t * pParsingContext = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );
    assert( pLoc != NULL );

    pParsingContext = ( HTTPParsingContext_t * ) ( pHttpParser->data );

    /* Set the location of what to parse next. */
    pParsingContext->pBufferCur = &pLoc[ length ];

    /* If httpParserOnHeaderValueCallback() is invoked in succession, then the
     * last time llhttp_execute() was called only part of the header field
     * was parsed. The indication of successive invocations is a non-NULL
     * pParsingContext->pLastHeaderField. */
    if( pParsingContext->pLastHeaderValue == NULL )
    {
        pParsingContext->pLastHeaderValue = pLoc;
        pParsingContext->lastHeaderValueLen = length;
    }
    else
    {
        pParsingContext->lastHeaderValueLen += length;
    }

    /* Given that httpParserOnHeaderFieldCallback() is ALWAYS invoked before
     * httpParserOnHeaderValueCallback() is invoked, then the last header field
     * should never be NULL. This would indicate a bug in the llhttp library. */
    assert( pParsingContext->pLastHeaderField != NULL );

    LogDebug( ( "Response parsing: Found a header value: "
                "HeaderValue=%.*s",
                ( int ) length,
                pLoc ) );

    return LLHTTP_CONTINUE_PARSING;
}

/*-----------------------------------------------------------*/

static int httpParserOnHeadersCompleteCallback( llhttp_t * pHttpParser )
{
    int shouldContinueParse = LLHTTP_CONTINUE_PARSING;
    HTTPParsingContext_t * pParsingContext = NULL;
    HTTPResponse_t * pResponse = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );

    pParsingContext = ( HTTPParsingContext_t * ) ( pHttpParser->data );
    pResponse = pParsingContext->pResponse;

    assert( pResponse != NULL );
    assert( pParsingContext->pBufferCur != NULL );

    /* Flag indicating that the headers have been completely signed - useful for libraries built on top of corehttp. */
    pResponse->areHeadersComplete = 1;

    /* The current location to parse was updated in previous callbacks and MUST
     * always be within the response buffer. */
    assert( pParsingContext->pBufferCur >= ( const char * ) ( pResponse->pBuffer ) );
    assert( pParsingContext->pBufferCur < ( const char * ) ( pResponse->pBuffer + pResponse->bufferLen ) );

    /* `\r\n\r\n`, `\r\n\n`, `\n\r\n`, and `\n\n` are all valid indicators of
     * the end of the response headers. To reduce complexity these characters
     * are not included in the response headers length returned to the user. */

    /* If headers existed, then pResponse->pHeaders was set during the first
     * call to httpParserOnHeaderFieldCallback(). */
    if( pResponse->pHeaders != NULL )
    {
        /* The start of the headers ALWAYS come before the the end of the headers. */
        assert( ( const char * ) ( pResponse->pHeaders ) < pParsingContext->pBufferCur );

        /* MISRA Ref 10.8.1 [Essential type casting] */
        /* More details at: https://github.com/FreeRTOS/coreHTTP/blob/main/MISRA.md#rule-108 */
        /* coverity[misra_c_2012_rule_10_8_violation] */
        pResponse->headersLen = ( size_t ) ( pParsingContext->pBufferCur - ( const char * ) ( pResponse->pHeaders ) );
    }
    else
    {
        pResponse->headersLen = 0U;
    }

    /* MISRA Ref 14.3.1 [Configuration dependent invariant] */
    /* More details at: https://github.com/FreeRTOS/coreHTTP/blob/main/MISRA.md#rule-143 */
    /* coverity[misra_c_2012_rule_14_3_violation] */
    if( pHttpParser->content_length != UINT64_MAX )
    {
        pResponse->contentLength = ( size_t ) ( pHttpParser->content_length );
    }
    else
    {
        pResponse->contentLength = 0U;
    }

    /* If the Connection: close header was found this flag will be set. */
    if( ( pHttpParser->flags & ( unsigned int ) ( F_CONNECTION_CLOSE ) ) != 0U )
    {
        pResponse->respFlags |= HTTP_RESPONSE_CONNECTION_CLOSE_FLAG;
    }

    /* If the Connection: keep-alive header was found this flag will be set. */
    if( ( pHttpParser->flags & ( unsigned int ) ( F_CONNECTION_KEEP_ALIVE ) ) != 0U )
    {
        pResponse->respFlags |= HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG;
    }

    /* llhttp_execute() requires that callback implementations must
     * indicate that parsing stops on headers complete, if response is to a HEAD
     * request. A HEAD response will contain Content-Length, but no body. If
     * the parser is not stopped here, then it will try to keep parsing past the
     * end of the headers up to the Content-Length found. */
    if( pParsingContext->isHeadResponse == 1U )
    {
        shouldContinueParse = LLHTTP_STOP_PARSING_NO_BODY;
    }

    /* If headers are present in the response, then
     * httpParserOnHeadersCompleteCallback() always follows
     * the httpParserOnHeaderValueCallback(). When
     * httpParserOnHeaderValueCallback() is not called in succession, then a
     * complete header has been found. */
    processCompleteHeader( pParsingContext );

    LogDebug( ( "Response parsing: Found the end of the headers." ) );

    /* If there is HTTP_RESPONSE_DO_NOT_PARSE_BODY_FLAG opt-in we should stop
     * parsing here. */
    if( ( pResponse->respOptionFlags & HTTP_RESPONSE_DO_NOT_PARSE_BODY_FLAG ) != 0U )
    {
        shouldContinueParse = ( int ) LLHTTP_PAUSE_PARSING;
    }

    return shouldContinueParse;
}

/*-----------------------------------------------------------*/

static int httpParserOnBodyCallback( llhttp_t * pHttpParser,
                                     const char * pLoc,
                                     size_t length )
{
    int shouldContinueParse = LLHTTP_CONTINUE_PARSING;
    HTTPParsingContext_t * pParsingContext = NULL;
    HTTPResponse_t * pResponse = NULL;
    char * pNextWriteLoc = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );
    assert( pLoc != NULL );

    pParsingContext = ( HTTPParsingContext_t * ) ( pHttpParser->data );
    pResponse = pParsingContext->pResponse;

    assert( pResponse != NULL );
    assert( pResponse->pBuffer != NULL );
    assert( pLoc >= ( const char * ) ( pResponse->pBuffer ) );
    assert( pLoc < ( const char * ) ( pResponse->pBuffer + pResponse->bufferLen ) );

    /* If this is the first time httpParserOnBodyCallback() has been invoked,
     * then the start of the response body is NULL. */
    if( pResponse->pBody == NULL )
    {
        /* Ideally the start of the body should follow right after the header
         * end indicating characters, but to reduce complexity and ensure users
         * are given the correct start of the body, we set the start of the body
         * to what the parser tells us is the start. This could come after the
         * initial transfer encoding chunked header. */
        pResponse->pBody = ( const uint8_t * ) ( pLoc );
        pResponse->bodyLen = 0U;
    }

    /* The next location to write. */

    /* MISRA Ref 11.8.1 [Removal of const from pointer] */
    /* More details at: https://github.com/FreeRTOS/coreHTTP/blob/main/MISRA.md#rule-118 */
    /* coverity[misra_c_2012_rule_11_8_violation] */
    pNextWriteLoc = ( char * ) ( &( pResponse->pBody[ pResponse->bodyLen ] ) );

    /* If the response is of type Transfer-Encoding: chunked, then actual body
     * will follow the the chunked header. This body data is in a later location
     * and must be moved up in the buffer. When pLoc is greater than the current
     * end of the body, that signals the parser found a chunk header. */

    /* MISRA Ref 18.3.1 [Pointer comparison] */
    /* More details at: https://github.com/FreeRTOS/coreHTTP/blob/main/MISRA.md#rule-183 */
    /* coverity[pointer_parameter] */
    /* coverity[misra_c_2012_rule_18_3_violation] */
    if( pLoc > pNextWriteLoc )
    {
        /* memmove is used instead of memcpy because memcpy has undefined behavior
         * when source and destination locations in memory overlap. */
        ( void ) memmove( pNextWriteLoc, pLoc, length );
    }

    /* Increase the length of the body found. */
    pResponse->bodyLen += length;

    /* Set the next location of parsing. */
    pParsingContext->pBufferCur = &pLoc[ length ];

    LogDebug( ( "Response parsing: Found the response body: "
                "BodyLength=%lu",
                ( unsigned long ) length ) );

    return shouldContinueParse;
}

/*-----------------------------------------------------------*/

static int httpParserOnMessageCompleteCallback( llhttp_t * pHttpParser )
{
    HTTPParsingContext_t * pParsingContext = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );

    pParsingContext = ( HTTPParsingContext_t * ) ( pHttpParser->data );

    /* The response message is complete. */
    pParsingContext->state = HTTP_PARSING_COMPLETE;

    LogDebug( ( "Response parsing: Response message complete." ) );

    return LLHTTP_CONTINUE_PARSING;
}

/*-----------------------------------------------------------*/

static void initializeParsingContextForFirstResponse( HTTPParsingContext_t * pParsingContext,
                                                      const HTTPRequestHeaders_t * pRequestHeaders )
{
    assert( pParsingContext != NULL );
    assert( pRequestHeaders != NULL );
    assert( pRequestHeaders->headersLen >= HTTP_MINIMUM_REQUEST_LINE_LENGTH );

    /* Initialize the callbacks that llhttp_execute will invoke. */
    llhttp_settings_init( &( pParsingContext->llhttpSettings ) );
    pParsingContext->llhttpSettings.on_message_begin = &httpParserOnMessageBeginCallback;
    pParsingContext->llhttpSettings.on_status = &httpParserOnStatusCallback;
    pParsingContext->llhttpSettings.on_status_complete = &httpParserOnStatusCompleteCallback;
    pParsingContext->llhttpSettings.on_header_field = &httpParserOnHeaderFieldCallback;
    pParsingContext->llhttpSettings.on_header_value = &httpParserOnHeaderValueCallback;
    pParsingContext->llhttpSettings.on_headers_complete = &httpParserOnHeadersCompleteCallback;
    pParsingContext->llhttpSettings.on_body = &httpParserOnBodyCallback;
    pParsingContext->llhttpSettings.on_message_complete = &httpParserOnMessageCompleteCallback;

    /* Initialize the third-party HTTP parser to parse responses. */
    llhttp_init( &( pParsingContext->llhttpParser ), HTTP_RESPONSE, &( pParsingContext->llhttpSettings ) );

    /* No response has been parsed yet. */
    pParsingContext->state = HTTP_PARSING_NONE;

    /* No response to update is associated with this parsing context yet. */
    pParsingContext->pResponse = NULL;

    /* The parsing context needs to know if the expected response is to a HEAD
     * request. For a HEAD response, the third-party parser requires parsing is
     * indicated to stop by returning a 1 from httpParserOnHeadersCompleteCallback().
     * If this is not done, the parser will not indicate the message is complete. */
    if( strncmp( ( const char * ) ( pRequestHeaders->pBuffer ),
                 HTTP_METHOD_HEAD,
                 sizeof( HTTP_METHOD_HEAD ) - 1U ) == 0 )
    {
        pParsingContext->isHeadResponse = 1U;
    }
}

/*-----------------------------------------------------------*/

static HTTPStatus_t processLlhttpError( const llhttp_t * pHttpParser )
{
    HTTPStatus_t returnStatus = HTTPSuccess;

    assert( pHttpParser != NULL );

    /* llhttp_get_err_pos() may be used to get exact error locations, which was
     * not possible with the previous http-parser. */

    switch( llhttp_get_errno( pHttpParser ) )
    {
        case HPE_OK:
        case HPE_PAUSED_UPGRADE:
            /* There were no errors. */
            break;

        case HPE_INVALID_EOF_STATE:

            /* In this case the parser was passed a length of zero, which indicates
             * an EOF from the server, in the middle of parsing the response.
             * This case is already handled by checking HTTPParsingContext_t.state. */
            break;

        /* No header overflow in llhttp since no header size was set. */

        case HPE_CLOSED_CONNECTION:
            LogError( ( "Response parsing error: Data received past complete "
                        "response with \"Connection: close\" header present." ) );
            returnStatus = HTTPSecurityAlertExtraneousResponseData;
            break;

        case HPE_INVALID_CHUNK_SIZE:

            /* http_parser_execute() does not give feedback on the exact failing
             * character and location. */
            LogError( ( "Response parsing error: Invalid character found in "
                        "chunk header." ) );
            returnStatus = HTTPSecurityAlertInvalidChunkHeader;
            break;

        case HPE_INVALID_VERSION:

            /* http_parser_execute() does not give feedback on the exact failing
             * character and location. */
            LogError( ( "Response parsing error: Invalid character found in "
                        "HTTP protocol version." ) );

            returnStatus = HTTPSecurityAlertInvalidProtocolVersion;
            break;

        case HPE_INVALID_STATUS:

            /* There could be an invalid character or the status code number
             * could be out of range. This feedback is not given back by the
             * http-parser library. */
            LogError( ( "Response parsing error: Invalid Status code." ) );
            returnStatus = HTTPSecurityAlertInvalidStatusCode;
            break;

        case HPE_STRICT:
        case HPE_INVALID_CONSTANT:
            LogError( ( "Response parsing error: Invalid character found in "
                        "Status-Line or header delimiters." ) );
            returnStatus = HTTPSecurityAlertInvalidCharacter;
            break;

        case HPE_LF_EXPECTED:
            LogError( ( "Response parsing error: Expected line-feed in header "
                        "not found." ) );
            returnStatus = HTTPSecurityAlertInvalidCharacter;
            break;

        case HPE_INVALID_HEADER_TOKEN:

            /* http_parser_execute() does not give feedback on the exact failing
             * character and location. */
            LogError( ( "Response parsing error: Invalid character found in "
                        "headers." ) );
            returnStatus = HTTPSecurityAlertInvalidCharacter;
            break;

        case HPE_INVALID_CONTENT_LENGTH:

            /* http_parser_execute() does not give feedback on the exact failing
             * character and location. */
            LogError( ( "Response parsing error: Invalid character found in "
                        "content-length headers." ) );
            returnStatus = HTTPSecurityAlertInvalidContentLength;
            break;

        case HPE_UNEXPECTED_CONTENT_LENGTH:
            LogError( ( "Response parsing error: A Content-Length header was "
                        "found when it shouldn't have been." ) );
            returnStatus = HTTPSecurityAlertInvalidContentLength;
            break;

        case HPE_PAUSED:
            LogInfo( ( "User intervention: Parsing stopped by user." ) );
            returnStatus = HTTPParserPaused;
            break;

        /* All other error cases cannot be triggered and indicate an error in the
         * third-party parsing library if found. */
        default:
            LogError( ( "Error in third-party llhttp library: %s", llhttp_errno_name( llhttp_get_errno( pHttpParser ) ) ) );
            returnStatus = HTTPParserInternalError;
            break;
    }

    /* Errors with HPE_CB_ prepended are manual returns of non-zero in the
     * response parsing callback. */
    LogDebug( ( "llhttp errno description: %s %s",
                llhttp_errno_name( llhttp_get_errno( pHttpParser ) ),
                llhttp_get_error_reason( pHttpParser ) ) );

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t parseHttpResponse( HTTPParsingContext_t * pParsingContext,
                                       HTTPResponse_t * pResponse,
                                       size_t parseLen )
{
    HTTPStatus_t returnStatus;
    const char * parsingStartLoc = NULL;
    llhttp_errno_t eReturn;

    assert( pParsingContext != NULL );
    assert( pResponse != NULL );

    /* If this is the first time this parsing context is used, then set the
     * response input. */
    if( pParsingContext->pResponse == NULL )
    {
        pParsingContext->pResponse = pResponse;
        pParsingContext->pBufferCur = ( const char * ) pResponse->pBuffer;

        /* Initialize the status-code returned in the response. */
        pResponse->statusCode = 0U;
        /* Initialize the start of the response body and length. */
        pResponse->pBody = NULL;
        pResponse->bodyLen = 0U;

        /* Initialize the start of the headers, its length, and the count for
         * the parsing that follows the status. */
        pResponse->pHeaders = NULL;
        pResponse->headersLen = 0U;
        pResponse->headerCount = 0U;
        /* Initialize the response flags. */
        pResponse->respFlags = 0U;
    }
    else
    {
        /* This function is currently private to the HTTP Client library. It is
         * therefore a development bug to have this function invoked in
         * succession without the same response. */
        assert( pParsingContext->pResponse == pResponse );
    }

    /* Setting this allows the parsing context and response to be carried to
     * each of the callbacks that llhttp_execute() will invoke. */
    pParsingContext->llhttpParser.data = pParsingContext;

    /* Save the starting response buffer location to parse. This is needed to
     * ensure that we move the next location to parse to exactly how many
     * characters were parsed in this call. */
    parsingStartLoc = pParsingContext->pBufferCur;

    /* This will begin the parsing. Each of the callbacks set in
     * parserSettings will be invoked as parts of the HTTP response are
     * reached. The return code is parsed in #processLlhttpError. */
    eReturn = llhttp_execute( &( pParsingContext->llhttpParser ), parsingStartLoc, parseLen );

    if( eReturn == HPE_PAUSED_UPGRADE )
    {
        llhttp_resume_after_upgrade( &( pParsingContext->llhttpParser ) );
    }

    if( eReturn == HPE_PAUSED )
    {
        /* The next location to parse is where the parser was paused. */
        pParsingContext->pBufferCur = pParsingContext->llhttpParser.error_pos;
    }
    else
    {
        /* The next location to parse is after what has already been parsed. */
        pParsingContext->pBufferCur = &parsingStartLoc[ parseLen ];
    }

    returnStatus = processLlhttpError( &( pParsingContext->llhttpParser ) );

    return returnStatus;
}

/*-----------------------------------------------------------*/

static uint8_t convertInt32ToAscii( int32_t value,
                                    char * pBuffer,
                                    size_t bufferLength )
{
    /* As input value may be altered and MISRA C 2012 rule 17.8 prevents
     * modification of parameter, a local copy of the parameter is stored.
     * absoluteValue stores the positive version of the input value. Its type
     * remains the same type as the input value to avoid unnecessary casting on
     * a privately used variable. This variable's size will always be less
     * than INT32_MAX. */
    int32_t absoluteValue = value;
    uint8_t numOfDigits = 0U;
    uint8_t index = 0U;
    uint8_t isNegative = 0U;
    int32_t bufferIndex;
    char temp = '\0';

    assert( pBuffer != NULL );
    assert( bufferLength >= MAX_INT32_NO_OF_DECIMAL_DIGITS );
    ( void ) bufferLength;

    /* If the value is negative, write the '-' (minus) character to the buffer. */
    if( value < 0 )
    {
        isNegative = 1U;

        *pBuffer = '-';

        /* Convert the value to its absolute representation. */
        absoluteValue = value * ( -1 );
    }

    /* Write the absolute integer value in reverse ASCII representation. */
    do
    {
        pBuffer[ isNegative + numOfDigits ] = ( char ) ( ( absoluteValue % 10 ) + '0' );
        numOfDigits++;
        absoluteValue /= 10;
    } while( absoluteValue != 0 );

    /* Reverse the digits in the buffer to store the correct ASCII representation
     * of the value. */
    for( index = 0U; index < ( numOfDigits / 2U ); index++ )
    {
        temp = pBuffer[ isNegative + index ];
        bufferIndex = ( int32_t ) isNegative + ( int32_t ) numOfDigits - ( int32_t ) index - 1;
        pBuffer[ isNegative + index ] = pBuffer[ bufferIndex ];
        pBuffer[ bufferIndex ] = temp;
    }

    return ( uint8_t ) ( isNegative + numOfDigits );
}

/*-----------------------------------------------------------*/

static char * httpHeaderStrncpy( char * pDest,
                                 const char * pSrc,
                                 size_t len,
                                 uint8_t isField )
{
    size_t i = 0U;
    char * pRet = pDest;
    uint8_t hasError = 0U;

    assert( pDest != NULL );
    assert( pSrc != NULL );

    for( ; i < len; i++ )
    {
        if( pSrc[ i ] == CARRIAGE_RETURN_CHARACTER )
        {
            LogError( ( "Invalid character '\r' found in %.*s",
                        ( int ) len, pSrc ) );
            hasError = 1U;
        }
        else if( pSrc[ i ] == LINEFEED_CHARACTER )
        {
            LogError( ( "Invalid character '\n' found in %.*s",
                        ( int ) len, pSrc ) );
            hasError = 1U;
        }
        else if( ( isField == 1U ) && ( pSrc[ i ] == COLON_CHARACTER ) )
        {
            LogError( ( "Invalid character ':' found in %.*s",
                        ( int ) len, pSrc ) );
            hasError = 1U;
        }
        else
        {
            pDest[ i ] = pSrc[ i ];
        }

        if( hasError == 1U )
        {
            pRet = NULL;
            break;
        }
    }

    return pRet;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t addHeader( HTTPRequestHeaders_t * pRequestHeaders,
                               const char * pField,
                               size_t fieldLen,
                               const char * pValue,
                               size_t valueLen )
{
    HTTPStatus_t returnStatus = HTTPSuccess;
    char * pBufferCur = NULL;
    size_t toAddLen = 0U;
    size_t backtrackHeaderLen = 0U;

    /* Directly passing in these strings to memcpy is a MISRA Rule 7.4 violation
     * Due to this we allocate these pointers for MISRA compliance */
    const char * pHeaderEndIndicator = HTTP_HEADER_END_INDICATOR;
    const char * httpFieldSeparator = HTTP_HEADER_FIELD_SEPARATOR;

    assert( pRequestHeaders != NULL );
    assert( pRequestHeaders->pBuffer != NULL );
    assert( pField != NULL );
    assert( pValue != NULL );
    assert( fieldLen != 0U );
    assert( valueLen != 0U );

    pBufferCur = ( char * ) &( pRequestHeaders->pBuffer[ pRequestHeaders->headersLen ] );
    backtrackHeaderLen = pRequestHeaders->headersLen;

    /* Backtrack before trailing "\r\n" (HTTP header end) if it's already written.
     * Note that this method also writes trailing "\r\n" before returning.
     * The first condition prevents reading before start of the header. */
    if( ( HTTP_HEADER_END_INDICATOR_LEN <= pRequestHeaders->headersLen ) &&
        ( strncmp( ( char * ) &pBufferCur[ 0 - ( ( int ) HTTP_HEADER_END_INDICATOR_LEN ) ],
                   HTTP_HEADER_END_INDICATOR, HTTP_HEADER_END_INDICATOR_LEN ) == 0 ) )
    {
        backtrackHeaderLen -= HTTP_HEADER_LINE_SEPARATOR_LEN;
        pBufferCur = &pBufferCur[ 0 - ( ( int ) HTTP_HEADER_LINE_SEPARATOR_LEN ) ];
    }

    /* Check if there is enough space in buffer for additional header. */
    toAddLen = fieldLen + HTTP_HEADER_FIELD_SEPARATOR_LEN + valueLen +
               HTTP_HEADER_LINE_SEPARATOR_LEN +
               HTTP_HEADER_LINE_SEPARATOR_LEN;

    /* If we have enough room for the new header line, then write it to the
     * header buffer. */
    if( ( backtrackHeaderLen + toAddLen ) <= pRequestHeaders->bufferLen )
    {
        /* Write "<Field>: <Value> \r\n" to the headers buffer. */

        /* Copy the header name into the buffer. */
        if( httpHeaderStrncpy( pBufferCur, pField, fieldLen, HTTP_HEADER_STRNCPY_IS_FIELD ) == NULL )
        {
            returnStatus = HTTPSecurityAlertInvalidCharacter;
        }

        if( returnStatus == HTTPSuccess )
        {
            pBufferCur = &pBufferCur[ fieldLen ];

            /* Copy the field separator, ": ", into the buffer. */
            ( void ) memcpy( pBufferCur,
                             httpFieldSeparator,
                             HTTP_HEADER_FIELD_SEPARATOR_LEN );

            pBufferCur = &pBufferCur[ HTTP_HEADER_FIELD_SEPARATOR_LEN ];

            /* Copy the header value into the buffer. */
            if( httpHeaderStrncpy( pBufferCur, pValue, valueLen, HTTP_HEADER_STRNCPY_IS_VALUE ) == NULL )
            {
                returnStatus = HTTPSecurityAlertInvalidCharacter;
            }
        }

        if( returnStatus == HTTPSuccess )
        {
            pBufferCur = &pBufferCur[ valueLen ];

            /* Copy the header end indicator, "\r\n\r\n" into the buffer. */
            ( void ) memcpy( pBufferCur,
                             pHeaderEndIndicator,
                             HTTP_HEADER_END_INDICATOR_LEN );

            /* Update the headers length value only when everything is successful. */
            pRequestHeaders->headersLen = backtrackHeaderLen + toAddLen;
        }
    }
    else
    {
        LogError( ( "Unable to add header in buffer: "
                    "Buffer has insufficient memory: "
                    "RequiredBytes=%lu, RemainingBufferSize=%lu",
                    ( unsigned long ) toAddLen,
                    ( unsigned long ) ( pRequestHeaders->bufferLen - pRequestHeaders->headersLen ) ) );
        returnStatus = HTTPInsufficientMemory;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t addRangeHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                    int32_t rangeStartOrlastNbytes,
                                    int32_t rangeEnd )
{
    HTTPStatus_t returnStatus = HTTPSuccess;
    char rangeValueBuffer[ HTTP_MAX_RANGE_REQUEST_VALUE_LEN ];
    size_t rangeValueLength = 0U;

    /* Directly passing in these strings to memcpy is a MISRA Rule 7.4 violation
     * Due to this we allocate these pointers for MISRA compliance */
    const char * pHttpRangeRequestHeaderValuePrefix = HTTP_RANGE_REQUEST_HEADER_VALUE_PREFIX;
    const char * pHttpRangeRequestHeaderField = HTTP_RANGE_REQUEST_HEADER_FIELD;

    assert( pRequestHeaders != NULL );

    /* This buffer uses a char type instead of the general purpose uint8_t
     * because the range value expected to be written is within the ASCII
     * character set. */
    ( void ) memset( rangeValueBuffer, 0, HTTP_MAX_RANGE_REQUEST_VALUE_LEN );

    /* Generate the value data for the Range Request header.*/

    /* Write the range value prefix in the buffer. */
    ( void ) memcpy( rangeValueBuffer,
                     pHttpRangeRequestHeaderValuePrefix,
                     HTTP_RANGE_REQUEST_HEADER_VALUE_PREFIX_LEN );
    rangeValueLength += HTTP_RANGE_REQUEST_HEADER_VALUE_PREFIX_LEN;

    /* Write the range start value in the buffer. */
    rangeValueLength += convertInt32ToAscii( rangeStartOrlastNbytes,
                                             &rangeValueBuffer[ rangeValueLength ],
                                             sizeof( rangeValueBuffer ) - rangeValueLength );

    /* Add remaining value data depending on the range specification type. */

    /* Add rangeEnd value if request is for [rangeStart, rangeEnd] byte range */
    if( rangeEnd != HTTP_RANGE_REQUEST_END_OF_FILE )
    {
        /* Write the "-" character to the buffer.*/
        rangeValueBuffer[ rangeValueLength ] = DASH_CHARACTER;
        rangeValueLength += DASH_CHARACTER_LEN;

        /* Write the rangeEnd value of the request range to the buffer. */
        rangeValueLength += convertInt32ToAscii( rangeEnd,
                                                 &rangeValueBuffer[ rangeValueLength ],
                                                 sizeof( rangeValueBuffer ) - rangeValueLength );
    }
    /* Case when request is for bytes in the range [rangeStart, EoF). */
    else if( rangeStartOrlastNbytes >= 0 )
    {
        /* Write the "-" character to the buffer.*/
        rangeValueBuffer[ rangeValueLength ] = DASH_CHARACTER;
        rangeValueLength += DASH_CHARACTER_LEN;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    /* Add the Range Request header field and value to the buffer. */
    returnStatus = addHeader( pRequestHeaders,
                              pHttpRangeRequestHeaderField,
                              HTTP_RANGE_REQUEST_HEADER_FIELD_LEN,
                              rangeValueBuffer,
                              rangeValueLength );

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t writeRequestLine( HTTPRequestHeaders_t * pRequestHeaders,
                                      const char * pMethod,
                                      size_t methodLen,
                                      const char * pPath,
                                      size_t pathLen )
{
    HTTPStatus_t returnStatus = HTTPSuccess;
    char * pBufferCur = NULL;
    size_t toAddLen = 0U;

    /* Directly passing in these strings to memcpy is a MISRA Rule 7.4 violation
     * Due to this we allocate these pointers for MISRA compliance */
    const char * pHeaderLineSeparator = HTTP_HEADER_LINE_SEPARATOR;
    const char * pHttpProtocolVersion = HTTP_PROTOCOL_VERSION;
    const char * pHttpEmptyPath = HTTP_EMPTY_PATH;

    assert( pRequestHeaders != NULL );
    assert( pRequestHeaders->pBuffer != NULL );
    assert( pMethod != NULL );
    assert( methodLen != 0U );

    toAddLen = methodLen +                 \
               SPACE_CHARACTER_LEN +       \
               SPACE_CHARACTER_LEN +       \
               HTTP_PROTOCOL_VERSION_LEN + \
               HTTP_HEADER_LINE_SEPARATOR_LEN;

    pBufferCur = ( char * ) ( pRequestHeaders->pBuffer );
    toAddLen += ( ( pPath == NULL ) || ( pathLen == 0U ) ) ? HTTP_EMPTY_PATH_LEN : pathLen;

    if( ( toAddLen + pRequestHeaders->headersLen ) > pRequestHeaders->bufferLen )
    {
        returnStatus = HTTPInsufficientMemory;
    }

    if( returnStatus == HTTPSuccess )
    {
        /* Write "<METHOD> <PATH> HTTP/1.1\r\n" to start the HTTP header. */
        ( void ) memcpy( pBufferCur, pMethod, methodLen );
        pBufferCur = &pBufferCur[ methodLen ];

        *pBufferCur = SPACE_CHARACTER;
        pBufferCur = &pBufferCur[ SPACE_CHARACTER_LEN ];

        /* Use "/" as default value if <PATH> is NULL. */
        if( ( pPath == NULL ) || ( pathLen == 0U ) )
        {
            ( void ) memcpy( pBufferCur,
                             pHttpEmptyPath,
                             HTTP_EMPTY_PATH_LEN );
            pBufferCur = &pBufferCur[ HTTP_EMPTY_PATH_LEN ];
        }
        else
        {
            ( void ) memcpy( pBufferCur, pPath, pathLen );
            pBufferCur = &pBufferCur[ pathLen ];
        }

        *pBufferCur = SPACE_CHARACTER;
        pBufferCur = &pBufferCur[ SPACE_CHARACTER_LEN ];

        ( void ) memcpy( pBufferCur,
                         pHttpProtocolVersion,
                         HTTP_PROTOCOL_VERSION_LEN );
        pBufferCur = &pBufferCur[ HTTP_PROTOCOL_VERSION_LEN ];
        ( void ) memcpy( pBufferCur,
                         pHeaderLineSeparator,
                         HTTP_HEADER_LINE_SEPARATOR_LEN );
        pRequestHeaders->headersLen = toAddLen;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_InitializeRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders,
                                                  const HTTPRequestInfo_t * pRequestInfo )
{
    HTTPStatus_t returnStatus = HTTPSuccess;

    /* Check for NULL parameters. */
    if( pRequestHeaders == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pRequestHeaders->pBuffer == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->pBuffer is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pRequestInfo == NULL )
    {
        LogError( ( "Parameter check failed: pRequestInfo is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pRequestInfo->pMethod == NULL )
    {
        LogError( ( "Parameter check failed: pRequestInfo->pMethod is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pRequestInfo->pHost == NULL )
    {
        LogError( ( "Parameter check failed: pRequestInfo->pHost is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pRequestInfo->methodLen == 0U )
    {
        LogError( ( "Parameter check failed: pRequestInfo->methodLen must be greater than 0." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pRequestInfo->hostLen == 0U )
    {
        LogError( ( "Parameter check failed: pRequestInfo->hostLen must be greater than 0." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    if( returnStatus == HTTPSuccess )
    {
        /* Reset application-provided parameters. */
        pRequestHeaders->headersLen = 0U;

        /* Write "<METHOD> <PATH> HTTP/1.1\r\n" to start the HTTP header. */
        returnStatus = writeRequestLine( pRequestHeaders,
                                         pRequestInfo->pMethod,
                                         pRequestInfo->methodLen,
                                         pRequestInfo->pPath,
                                         pRequestInfo->pathLen );
    }

    if( returnStatus == HTTPSuccess )
    {
        if( ( HTTP_REQUEST_NO_USER_AGENT_FLAG & pRequestInfo->reqFlags ) == 0U )
        {
            /* Write "User-Agent: <Value>". */
            returnStatus = addHeader( pRequestHeaders,
                                      HTTP_USER_AGENT_FIELD,
                                      HTTP_USER_AGENT_FIELD_LEN,
                                      HTTP_USER_AGENT_VALUE,
                                      HTTP_USER_AGENT_VALUE_LEN );
        }
    }

    if( returnStatus == HTTPSuccess )
    {
        /* Write "Host: <Value>". */
        returnStatus = addHeader( pRequestHeaders,
                                  HTTP_HOST_FIELD,
                                  HTTP_HOST_FIELD_LEN,
                                  pRequestInfo->pHost,
                                  pRequestInfo->hostLen );
    }

    if( returnStatus == HTTPSuccess )
    {
        if( ( HTTP_REQUEST_KEEP_ALIVE_FLAG & pRequestInfo->reqFlags ) != 0U )
        {
            /* Write "Connection: keep-alive". */
            returnStatus = addHeader( pRequestHeaders,
                                      HTTP_CONNECTION_FIELD,
                                      HTTP_CONNECTION_FIELD_LEN,
                                      HTTP_CONNECTION_KEEP_ALIVE_VALUE,
                                      HTTP_CONNECTION_KEEP_ALIVE_VALUE_LEN );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_AddHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                   const char * pField,
                                   size_t fieldLen,
                                   const char * pValue,
                                   size_t valueLen )
{
    HTTPStatus_t returnStatus = HTTPSuccess;

    /* Check for NULL parameters. */
    if( pRequestHeaders == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pRequestHeaders->pBuffer == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->pBuffer is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pField == NULL )
    {
        LogError( ( "Parameter check failed: pField is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pValue == NULL )
    {
        LogError( ( "Parameter check failed: pValue is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( fieldLen == 0U )
    {
        LogError( ( "Parameter check failed: fieldLen must be greater than 0." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( valueLen == 0U )
    {
        LogError( ( "Parameter check failed: valueLen must be greater than 0." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pRequestHeaders->headersLen > pRequestHeaders->bufferLen )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->headersLen > pRequestHeaders->bufferLen." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    if( returnStatus == HTTPSuccess )
    {
        returnStatus = addHeader( pRequestHeaders,
                                  pField, fieldLen, pValue, valueLen );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_AddRangeHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                        int32_t rangeStartOrlastNbytes,
                                        int32_t rangeEnd )
{
    HTTPStatus_t returnStatus = HTTPSuccess;

    if( pRequestHeaders == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pRequestHeaders->pBuffer == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->pBuffer is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pRequestHeaders->headersLen > pRequestHeaders->bufferLen )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->headersLen > pRequestHeaders->bufferLen." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( rangeEnd < HTTP_RANGE_REQUEST_END_OF_FILE )
    {
        LogError( ( "Parameter check failed: rangeEnd is invalid: "
                    "rangeEnd should be >=-1: RangeEnd=%ld", ( long int ) rangeEnd ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( ( rangeStartOrlastNbytes < 0 ) &&
             ( rangeEnd != HTTP_RANGE_REQUEST_END_OF_FILE ) )
    {
        LogError( ( "Parameter check failed: Invalid range values: "
                    "rangeEnd should be -1 when rangeStart < 0: "
                    "RangeStart=%ld, RangeEnd=%ld",
                    ( long int ) rangeStartOrlastNbytes, ( long int ) rangeEnd ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( ( rangeEnd != HTTP_RANGE_REQUEST_END_OF_FILE ) &&
             ( rangeStartOrlastNbytes > rangeEnd ) )
    {
        LogError( ( "Parameter check failed: Invalid range values: "
                    "rangeStart should be < rangeEnd when both are >= 0: "
                    "RangeStart=%ld, RangeEnd=%ld",
                    ( long int ) rangeStartOrlastNbytes, ( long int ) rangeEnd ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( rangeStartOrlastNbytes == INT32_MIN )
    {
        LogError( ( "Parameter check failed: Arithmetic overflow detected: "
                    "rangeStart should be > -2147483648 (INT32_MIN): "
                    "RangeStart=%ld",
                    ( long int ) rangeStartOrlastNbytes ) );
        returnStatus = HTTPInvalidParameter;
    }
    else
    {
        returnStatus = addRangeHeader( pRequestHeaders,
                                       rangeStartOrlastNbytes,
                                       rangeEnd );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_SendHttpData( const TransportInterface_t * pTransport,
                                      HTTPClient_GetCurrentTimeFunc_t getTimestampMs,
                                      const uint8_t * pData,
                                      size_t dataLen )
{
    HTTPStatus_t returnStatus = HTTPSuccess;
    const uint8_t * pIndex = pData;
    int32_t bytesSent = 0;
    size_t bytesRemaining = dataLen;
    uint32_t lastSendTimeMs = 0U, timeSinceLastSendMs = 0U;
    uint32_t retryTimeoutMs = HTTP_SEND_RETRY_TIMEOUT_MS;

    assert( pTransport != NULL );
    assert( pTransport->send != NULL );
    assert( pData != NULL );

    /* If the timestamp function was undefined by the application, then do not
     * retry the transport send. */
    if( getTimestampMs == &getZeroTimestampMs )
    {
        retryTimeoutMs = 0U;
    }

    /* Initialize the last send time to allow retries, if 0 bytes are sent on
     * the first try. */
    lastSendTimeMs = getTimestampMs();

    /* Loop until all data is sent. */
    while( ( bytesRemaining > 0UL ) && ( returnStatus != HTTPNetworkError ) )
    {
        bytesSent = pTransport->send( pTransport->pNetworkContext,
                                      pIndex,
                                      bytesRemaining );

        /* BytesSent less than zero is an error. */
        if( bytesSent < 0 )
        {
            LogError( ( "Failed to send data: Transport send error: "
                        "TransportStatus=%ld", ( long int ) bytesSent ) );
            returnStatus = HTTPNetworkError;
        }
        else if( bytesSent > 0 )
        {
            /* It is a bug in the application's transport send implementation if
             * more bytes than expected are sent. To avoid a possible overflow
             * in converting bytesRemaining from unsigned to signed, this assert
             * must exist after the check for bytesSent being negative. */
            assert( ( size_t ) bytesSent <= bytesRemaining );

            /* Record the most recent time of successful transmission. */
            lastSendTimeMs = getTimestampMs();

            bytesRemaining -= ( size_t ) bytesSent;
            pIndex = &pIndex[ bytesSent ];
            LogDebug( ( "Sent data over the transport: "
                        "BytesSent=%ld, BytesRemaining=%lu, TotalBytesSent=%lu",
                        ( long int ) bytesSent,
                        ( unsigned long ) bytesRemaining,
                        ( unsigned long ) ( dataLen - bytesRemaining ) ) );
        }
        else
        {
            /* No bytes were sent over the network. */
            timeSinceLastSendMs = getTimestampMs() - lastSendTimeMs;

            /* Check for timeout if we have been waiting to send any data over
             * the network. */
            if( timeSinceLastSendMs >= retryTimeoutMs )
            {
                LogError( ( "Unable to send packet: Timed out in transport send." ) );
                returnStatus = HTTPNetworkError;
            }
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t addContentLengthHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                            size_t contentLength )
{
    HTTPStatus_t returnStatus = HTTPSuccess;
    char pContentLengthValue[ MAX_INT32_NO_OF_DECIMAL_DIGITS ] = { '\0' };
    uint8_t contentLengthValueNumBytes = 0U;

    assert( pRequestHeaders != NULL );
    assert( contentLength > 0U );

    contentLengthValueNumBytes = convertInt32ToAscii( ( int32_t ) contentLength,
                                                      pContentLengthValue,
                                                      sizeof( pContentLengthValue ) );

    returnStatus = addHeader( pRequestHeaders,
                              HTTP_CONTENT_LENGTH_FIELD,
                              HTTP_CONTENT_LENGTH_FIELD_LEN,
                              pContentLengthValue,
                              contentLengthValueNumBytes );

    if( returnStatus != HTTPSuccess )
    {
        LogError( ( "Failed to write Content-Length header to the request "
                    "header buffer: ContentLengthValue: %lu",
                    ( unsigned long ) contentLength ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_SendHttpHeaders( const TransportInterface_t * pTransport,
                                         HTTPClient_GetCurrentTimeFunc_t getTimestampMs,
                                         HTTPRequestHeaders_t * pRequestHeaders,
                                         size_t reqBodyLen,
                                         uint32_t sendFlags )
{
    HTTPStatus_t returnStatus = HTTPSuccess;
    uint8_t shouldSendContentLength = 0U;

    assert( pTransport != NULL );
    assert( pTransport->send != NULL );
    assert( pRequestHeaders != NULL );

    /* Send the content length header if the flag to disable is not set and the
     * body length is greater than zero. */
    shouldSendContentLength = ( ( ( sendFlags & HTTP_SEND_DISABLE_CONTENT_LENGTH_FLAG ) == 0U ) &&
                                ( reqBodyLen > 0U ) ) ? 1U : 0U;

    if( shouldSendContentLength == 1U )
    {
        returnStatus = addContentLengthHeader( pRequestHeaders, reqBodyLen );
    }

    if( returnStatus == HTTPSuccess )
    {
        LogDebug( ( "Sending HTTP request headers: HeaderBytes=%lu",
                    ( unsigned long ) ( pRequestHeaders->headersLen ) ) );
        returnStatus = HTTPClient_SendHttpData( pTransport,
                                                getTimestampMs,
                                                pRequestHeaders->pBuffer,
                                                pRequestHeaders->headersLen );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t sendHttpBody( const TransportInterface_t * pTransport,
                                  HTTPClient_GetCurrentTimeFunc_t getTimestampMs,
                                  const uint8_t * pRequestBodyBuf,
                                  size_t reqBodyBufLen )
{
    HTTPStatus_t returnStatus = HTTPSuccess;

    assert( pTransport != NULL );
    assert( pTransport->send != NULL );
    assert( pRequestBodyBuf != NULL );

    /* Send the request body. */
    LogDebug( ( "Sending the HTTP request body: BodyBytes=%lu",
                ( unsigned long ) reqBodyBufLen ) );
    returnStatus = HTTPClient_SendHttpData( pTransport, getTimestampMs, pRequestBodyBuf, reqBodyBufLen );

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t getFinalResponseStatus( HTTPParsingState_t parsingState,
                                            size_t totalReceived,
                                            const HTTPResponse_t * pResponse )
{
    HTTPStatus_t returnStatus = HTTPSuccess;

    assert( parsingState <= HTTP_PARSING_COMPLETE );
    assert( totalReceived <= pResponse->bufferLen );

    /* If no parsing occurred, that means network data was never received. */
    if( parsingState == HTTP_PARSING_NONE )
    {
        LogError( ( "Response not received: Zero returned from "
                    "transport recv: totalReceived=%lu",
                    ( unsigned long ) totalReceived ) );
        returnStatus = HTTPNoResponse;
    }
    else if( parsingState == HTTP_PARSING_INCOMPLETE )
    {
        /* HTTP_PARSING_INCOMPLETE is okay when HTTP_RESPONSE_DO_NOT_PARSE_BODY_FLAG is set
         * as the body data may yet to be read from the transport. */
        if( ( pResponse->respOptionFlags & HTTP_RESPONSE_DO_NOT_PARSE_BODY_FLAG ) == 0U )
        {
            if( totalReceived == pResponse->bufferLen )
            {
                LogError( ( "Cannot receive complete response from transport"
                            " interface: Response buffer has insufficient "
                            "space: responseBufferLen=%lu",
                            ( unsigned long ) pResponse->bufferLen ) );
                returnStatus = HTTPInsufficientMemory;
            }
            else
            {
                LogError( ( "Received partial response from transport "
                            "receive(): ResponseSize=%lu, TotalBufferSize=%lu",
                            ( unsigned long ) totalReceived,
                            ( unsigned long ) ( pResponse->bufferLen - totalReceived ) ) );
                returnStatus = HTTPPartialResponse;
            }
        }
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_ReceiveAndParseHttpResponse( const TransportInterface_t * pTransport,
                                                     HTTPResponse_t * pResponse,
                                                     const HTTPRequestHeaders_t * pRequestHeaders )
{
    HTTPStatus_t returnStatus = HTTPSuccess;
    size_t totalReceived = 0U;
    int32_t currentReceived = 0;
    HTTPParsingContext_t parsingContext = { 0 };
    uint8_t shouldRecv = 1U, shouldParse = 1U, timeoutReached = 0U;
    uint32_t lastRecvTimeMs = 0U, timeSinceLastRecvMs = 0U;
    uint32_t retryTimeoutMs = HTTP_RECV_RETRY_TIMEOUT_MS;

    assert( pTransport != NULL );
    assert( pTransport->recv != NULL );
    assert( pResponse != NULL );
    assert( pRequestHeaders != NULL );

    /* Initialize the parsing context for parsing the response received from the
     * network. */
    initializeParsingContextForFirstResponse( &parsingContext, pRequestHeaders );

    /* If the timestamp function was undefined by the application, then do not
     * retry the transport receive. */
    if( pResponse->getTime == &getZeroTimestampMs )
    {
        retryTimeoutMs = 0U;
    }

    /* Initialize the last send time to allow retries, if 0 bytes are sent on
     * the first try. */
    lastRecvTimeMs = pResponse->getTime();

    while( shouldRecv == 1U )
    {
        /* Receive the HTTP response data into the pResponse->pBuffer. */
        currentReceived = pTransport->recv( pTransport->pNetworkContext,
                                            &( pResponse->pBuffer[ totalReceived ] ),
                                            pResponse->bufferLen - totalReceived );

        /* Transport receive errors are negative. */
        if( currentReceived < 0 )
        {
            LogError( ( "Failed to receive HTTP data: Transport recv() "
                        "returned error: TransportStatus=%ld",
                        ( long int ) currentReceived ) );
            returnStatus = HTTPNetworkError;

            /* Do not invoke the parser on network errors. */
            shouldParse = 0U;
        }
        else if( currentReceived > 0 )
        {
            /* Reset the time of the last data received when data is received. */
            lastRecvTimeMs = pResponse->getTime();

            /* Parsing is done on data as soon as it is received from the network.
             * Because we cannot know how large the HTTP response will be in
             * total, parsing will tell us if the end of the message is reached.*/
            shouldParse = 1U;

            /* MISRA compliance requires the cast to an unsigned type, since we have checked that
             * the value of current received is greater than 0 we don't need to worry about int overflow. */
            totalReceived += ( size_t ) currentReceived;
        }
        else
        {
            timeSinceLastRecvMs = pResponse->getTime() - lastRecvTimeMs;
            /* Do not invoke the response parsing for intermediate zero data. */
            shouldParse = 0U;

            /* Check if the allowed elapsed time between non-zero data has been
             * reached. */
            if( timeSinceLastRecvMs >= retryTimeoutMs )
            {
                /* Invoke the parsing upon this final zero data to indicate
                 * to the parser that there is no more data available from the
                 * server. */
                shouldParse = 1U;
                timeoutReached = 1U;
            }
        }

        if( shouldParse == 1U )
        {
            /* Data is received into the buffer is immediately parsed. Parsing
             * is invoked even with a length of zero. A length of zero indicates
             * to the parser that there is no more data from the server (EOF).
             * Additionally MISRA compliance requires the cast to a larger type, but since we
             * know that the value is greater than 0 we don't need to worry about int overflow. */
            returnStatus = parseHttpResponse( &parsingContext,
                                              pResponse,
                                              ( uint64_t ) currentReceived );
        }

        /* Reading should continue if there are no errors in the transport receive
         * or parsing, the retry on zero data timeout has not been reached, the
         * parser indicated the response message is not finished, and there is
         * room in the response buffer. */
        shouldRecv = ( ( returnStatus == HTTPSuccess ) &&
                       ( timeoutReached == 0U ) &&
                       ( parsingContext.state != HTTP_PARSING_COMPLETE ) &&
                       ( totalReceived < pResponse->bufferLen ) ) ? 1U : 0U;
    }

    if( ( returnStatus == HTTPParserPaused ) &&
        ( ( pResponse->respOptionFlags & HTTP_RESPONSE_DO_NOT_PARSE_BODY_FLAG ) != 0U ) )
    {
        returnStatus = HTTPSuccess;

        /* There may be dangling data if we parse with do not parse body flag.
         * We expose this data through body to let the applications access it. */
        pResponse->pBody = ( const uint8_t * ) parsingContext.pBufferCur;

        /* MISRA Ref 11.4.1 [Casting pointer to int] */
        /* More details at: https://github.com/FreeRTOS/coreHTTP/blob/main/MISRA.md#rule-114 */
        /* coverity[misra_c_2012_rule_11_4_violation] */
        pResponse->bodyLen = totalReceived - ( size_t ) ( ( ( uintptr_t ) pResponse->pBody ) - ( ( uintptr_t ) pResponse->pBuffer ) );
    }

    if( returnStatus == HTTPSuccess )
    {
        /* If there are errors in receiving from the network or during parsing,
         * the final status of the response message is derived from the state of
         * the parsing and how much data is in the buffer. */
        returnStatus = getFinalResponseStatus( parsingContext.state,
                                               totalReceived,
                                               pResponse );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t sendHttpRequest( const TransportInterface_t * pTransport,
                                     HTTPClient_GetCurrentTimeFunc_t getTimestampMs,
                                     HTTPRequestHeaders_t * pRequestHeaders,
                                     const uint8_t * pRequestBodyBuf,
                                     size_t reqBodyBufLen,
                                     uint32_t sendFlags )
{
    HTTPStatus_t returnStatus = HTTPSuccess;

    assert( pTransport != NULL );
    assert( pRequestHeaders != NULL );
    assert( ( pRequestBodyBuf != NULL ) ||
            ( ( pRequestBodyBuf == NULL ) && ( reqBodyBufLen == 0 ) ) );
    assert( getTimestampMs != NULL );

    /* Send the headers, which are at one location in memory. */
    returnStatus = HTTPClient_SendHttpHeaders( pTransport,
                                               getTimestampMs,
                                               pRequestHeaders,
                                               reqBodyBufLen,
                                               sendFlags );

    /* Send the body, which is at another location in memory. */
    if( returnStatus == HTTPSuccess )
    {
        if( pRequestBodyBuf != NULL )
        {
            returnStatus = sendHttpBody( pTransport,
                                         getTimestampMs,
                                         pRequestBodyBuf,
                                         reqBodyBufLen );
        }
        else
        {
            LogDebug( ( "A request body was not sent: pRequestBodyBuf is NULL." ) );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_Send( const TransportInterface_t * pTransport,
                              HTTPRequestHeaders_t * pRequestHeaders,
                              const uint8_t * pRequestBodyBuf,
                              size_t reqBodyBufLen,
                              HTTPResponse_t * pResponse,
                              uint32_t sendFlags )
{
    HTTPStatus_t returnStatus = HTTPInvalidParameter;

    if( pTransport == NULL )
    {
        LogError( ( "Parameter check failed: pTransport interface is NULL." ) );
    }
    else if( pTransport->send == NULL )
    {
        LogError( ( "Parameter check failed: pTransport->send is NULL." ) );
    }
    else if( pTransport->recv == NULL )
    {
        LogError( ( "Parameter check failed: pTransport->recv is NULL." ) );
    }
    else if( pRequestHeaders == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders is NULL." ) );
    }
    else if( pRequestHeaders->pBuffer == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->pBuffer is NULL." ) );
    }
    else if( pRequestHeaders->headersLen < HTTP_MINIMUM_REQUEST_LINE_LENGTH )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->headersLen "
                    "does not meet minimum the required length. "
                    "MinimumRequiredLength=%u, HeadersLength=%lu",
                    HTTP_MINIMUM_REQUEST_LINE_LENGTH,
                    ( unsigned long ) ( pRequestHeaders->headersLen ) ) );
    }
    else if( pRequestHeaders->headersLen > pRequestHeaders->bufferLen )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->headersLen > "
                    "pRequestHeaders->bufferLen." ) );
    }
    else if( pResponse == NULL )
    {
        LogError( ( "Parameter check failed: pResponse is NULL. " ) );
    }
    else if( pResponse->pBuffer == NULL )
    {
        LogError( ( "Parameter check failed: pResponse->pBuffer is NULL." ) );
    }
    else if( pResponse->bufferLen == 0U )
    {
        LogError( ( "Parameter check failed: pResponse->bufferLen is zero." ) );
    }
    else if( ( pRequestBodyBuf == NULL ) && ( reqBodyBufLen > 0U ) )
    {
        /* If there is no body to send we must ensure that the reqBodyBufLen is
         * zero so that no Content-Length header is automatically written. */
        LogError( ( "Parameter check failed: pRequestBodyBuf is NULL, but "
                    "reqBodyBufLen is greater than zero." ) );
    }
    else if( reqBodyBufLen > ( size_t ) ( INT32_MAX ) )
    {
        /* This check is needed because convertInt32ToAscii() is used on the
         * reqBodyBufLen to create a Content-Length header value string. */
        LogError( ( "Parameter check failed: reqBodyBufLen > INT32_MAX."
                    "reqBodyBufLen=%lu",
                    ( unsigned long ) reqBodyBufLen ) );
    }
    else
    {
        if( pResponse->getTime == NULL )
        {
            /* Set a zero timestamp function when the application did not configure
             * one. */
            pResponse->getTime = &getZeroTimestampMs;
        }

        returnStatus = HTTPSuccess;
    }

    if( returnStatus == HTTPSuccess )
    {
        returnStatus = sendHttpRequest( pTransport,
                                        pResponse->getTime,
                                        pRequestHeaders,
                                        pRequestBodyBuf,
                                        reqBodyBufLen,
                                        sendFlags );
    }

    if( returnStatus == HTTPSuccess )
    {
        returnStatus = HTTPClient_ReceiveAndParseHttpResponse( pTransport,
                                                               pResponse,
                                                               pRequestHeaders );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int findHeaderFieldParserCallback( llhttp_t * pHttpParser,
                                          const char * pFieldLoc,
                                          size_t fieldLen )
{
    findHeaderContext_t * pContext = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );
    assert( pFieldLoc != NULL );

    if( fieldLen == 0U )
    {
        LogError( ( "Received zero-length header field name from parser." ) );
        return LLHTTP_STOP_PARSING;
    }

    pContext = ( findHeaderContext_t * ) pHttpParser->data;

    assert( pContext->pField != NULL );
    assert( pContext->fieldLen > 0U );

    /* The header found flags should not be set. */
    assert( pContext->fieldFound == 0U );
    assert( pContext->valueFound == 0U );

    /* Check whether the parsed header matches the header we are looking for. */
    /* Each header field consists of a case-insensitive field name (RFC 7230, section 3.2). */
    if( ( fieldLen == pContext->fieldLen ) &&
        ( caseInsensitiveStringCmp( pContext->pField, pFieldLoc, fieldLen ) == 0 ) )
    {
        LogDebug( ( "Found header field in response: "
                    "HeaderName=%.*s, HeaderLocation=0x%p",
                    ( int ) fieldLen, pContext->pField, pFieldLoc ) );

        /* Set the flag to indicate that header has been found in response. */
        pContext->fieldFound = 1U;
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    return LLHTTP_CONTINUE_PARSING;
}

/*-----------------------------------------------------------*/

static int findHeaderValueParserCallback( llhttp_t * pHttpParser,
                                          const char * pValueLoc,
                                          size_t valueLen )
{
    int retCode = LLHTTP_CONTINUE_PARSING;
    findHeaderContext_t * pContext = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );
    assert( pValueLoc != NULL );

    pContext = ( findHeaderContext_t * ) pHttpParser->data;

    assert( pContext->pField != NULL );
    assert( pContext->fieldLen > 0U );
    assert( pContext->pValueLoc != NULL );
    assert( pContext->pValueLen != NULL );

    /* The header value found flag should not be set. */
    assert( pContext->valueFound == 0U );

    if( pContext->fieldFound == 1U )
    {
        LogDebug( ( "Found header value in response: "
                    "RequestedField=%.*s, ValueLocation=0x%p",
                    ( int ) ( pContext->fieldLen ), pContext->pField, pValueLoc ) );

        if( valueLen > 0U )
        {
            /* Populate the output parameters with the location of the header
             * value in the response buffer. */
            *pContext->pValueLoc = pValueLoc;
            *pContext->pValueLen = valueLen;
        }
        else
        {
            /* It is not invalid according to RFC 2616 to have an empty header
             * value. */
            *pContext->pValueLoc = NULL;
            *pContext->pValueLen = 0U;
        }

        /* Set the header value found flag. */
        pContext->valueFound = 1U;

        /* As we have found the value associated with the header, we don't need
         * to parse the response any further. */
        retCode = ( int ) LLHTTP_STOP_PARSING;
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    return retCode;
}

/*-----------------------------------------------------------*/

static int findHeaderOnHeaderCompleteCallback( llhttp_t * pHttpParser )
{
    const findHeaderContext_t * pContext = NULL;

    /* Disable unused parameter warning. */
    ( void ) pHttpParser;
    /* Disable unused variable warning. */
    ( void ) pContext;

    assert( pHttpParser != NULL );

    pContext = ( findHeaderContext_t * ) pHttpParser->data;

    /* If we have reached here, all headers in the response have been parsed but the requested
     * header has not been found in the response buffer. */
    LogDebug( ( "Reached end of header parsing: Header not found in response: "
                "RequestedHeader=%.*s",
                ( int ) ( pContext->fieldLen ),
                pContext->pField ) );

    /* No further parsing is required; thus, indicate the parser to stop parsing.
     * The documentation for on_headers_complete states that this function can
     * return 1 to indicate the response has no body, or -1 to indicate error.
     * Returning 1 causes llhttp_execute() to exit with success, while -1
     * causes it to return the HPE_CB_HEADERS_COMPLETE error code (in strict
     * mode) or success (in non-strict mode). We are fine with the success
     * return value, as llhttp_execute will not be invoked again in the same call.*/
    return LLHTTP_STOP_PARSING_NO_HEADER;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t findHeaderInResponse( const uint8_t * pBuffer,
                                          size_t bufferLen,
                                          const char * pField,
                                          size_t fieldLen,
                                          const char ** pValueLoc,
                                          size_t * pValueLen )
{
    HTTPStatus_t returnStatus = HTTPSuccess;
    llhttp_t parser = { 0 };
    llhttp_settings_t parserSettings = { 0 };
    llhttp_errno_t parserErrno;
    findHeaderContext_t context = { 0 };

    context.pField = pField;
    context.fieldLen = fieldLen;
    context.pValueLoc = pValueLoc;
    context.pValueLen = pValueLen;
    context.fieldFound = 0U;
    context.valueFound = 0U;

    /* The intention here to define callbacks just for searching the headers. We will
     * need to create a private context in llhttp->data that has the field and
     * value to update and pass back. */
    llhttp_settings_init( &parserSettings );
    parserSettings.on_header_field = &findHeaderFieldParserCallback;
    parserSettings.on_header_value = &findHeaderValueParserCallback;
    parserSettings.on_headers_complete = &findHeaderOnHeaderCompleteCallback;
    llhttp_init( &parser, HTTP_RESPONSE, &parserSettings );

    /* Set the context for the parser. */
    parser.data = &context;

    /* Search for the desired header. */
    parserErrno = llhttp_execute( &parser, ( const char * ) pBuffer, bufferLen );

    if( context.fieldFound == 0U )
    {
        /* If header field is not found, then both the flags should be zero. */
        assert( context.valueFound == 0U );

        /* Header is not present in buffer. */
        LogWarn( ( "Header not found in response buffer: RequestedHeader=%.*s",
                   ( int ) fieldLen,
                   pField ) );

        returnStatus = HTTPHeaderNotFound;
    }
    else if( context.valueFound == 0U )
    {
        /* The response buffer is invalid as only the header field was found
         * in the "<field>: <value>\r\n" format of an HTTP header. */
        LogError( ( "Unable to find header value in response: "
                    "Response data is invalid: "
                    "RequestedHeader=%.*s, ParserError=%s %s",
                    ( int ) fieldLen,
                    pField,
                    llhttp_errno_name( parserErrno ),
                    llhttp_get_error_reason( &parser ) ) );
        returnStatus = HTTPInvalidResponse;
    }
    else
    {
        /* Header is found. */
        assert( ( context.fieldFound == 1U ) && ( context.valueFound == 1U ) );

        LogDebug( ( "Found requested header in response: "
                    "HeaderName=%.*s, HeaderValue=%.*s",
                    ( int ) fieldLen,
                    pField,
                    ( int ) ( *pValueLen ),
                    *pValueLoc ) );
        returnStatus = HTTPSuccess;
    }

    /* If the header field-value pair is found in response, then the return
     * value of the on_header_value callback should set the llhttp.error to
     * HPE_USER. */
    if( ( returnStatus == HTTPSuccess ) &&
        ( parserErrno != HPE_USER ) )
    {
        LogError( ( "Header found in response but llhttp returned error: "
                    "ParserError=%s %s",
                    llhttp_errno_name( parserErrno ),
                    llhttp_get_error_reason( &parser ) ) );
        returnStatus = HTTPParserInternalError;
    }

    /* If header was not found, then the "on_header_complete" callback is
     * expected to be called which should set the llhttp.error to HPE_OK. */
    else if( ( returnStatus == HTTPHeaderNotFound ) &&
             ( parserErrno != HPE_OK ) )
    {
        LogError( ( "Header not found in response: llhttp returned error: "
                    "ParserError=%s %s",
                    llhttp_errno_name( parserErrno ),
                    llhttp_get_error_reason( &parser ) ) );
        returnStatus = HTTPInvalidResponse;
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_ReadHeader( const HTTPResponse_t * pResponse,
                                    const char * pField,
                                    size_t fieldLen,
                                    const char ** pValueLoc,
                                    size_t * pValueLen )
{
    HTTPStatus_t returnStatus = HTTPSuccess;

    if( pResponse == NULL )
    {
        LogError( ( "Parameter check failed: pResponse is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pResponse->pBuffer == NULL )
    {
        LogError( ( "Parameter check failed: pResponse->pBuffer is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pResponse->bufferLen == 0U )
    {
        LogError( ( "Parameter check failed: pResponse->bufferLen is 0: "
                    "Buffer len should be > 0." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pField == NULL )
    {
        LogError( ( "Parameter check failed: Input header name is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( fieldLen == 0U )
    {
        LogError( ( "Parameter check failed: Input header name length is 0: "
                    "fieldLen should be > 0." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pValueLoc == NULL )
    {
        LogError( ( "Parameter check failed: Output parameter for header value location is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else if( pValueLen == NULL )
    {
        LogError( ( "Parameter check failed: Output parameter for header value length is NULL." ) );
        returnStatus = HTTPInvalidParameter;
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    if( returnStatus == HTTPSuccess )
    {
        returnStatus = findHeaderInResponse( pResponse->pBuffer,
                                             pResponse->bufferLen,
                                             pField,
                                             fieldLen,
                                             pValueLoc,
                                             pValueLen );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

const char * HTTPClient_strerror( HTTPStatus_t status )
{
    const char * str = NULL;

    switch( status )
    {
        case HTTPSuccess:
            str = "HTTPSuccess";
            break;

        case HTTPInvalidParameter:
            str = "HTTPInvalidParameter";
            break;

        case HTTPNetworkError:
            str = "HTTPNetworkError";
            break;

        case HTTPPartialResponse:
            str = "HTTPPartialResponse";
            break;

        case HTTPNoResponse:
            str = "HTTPNoResponse";
            break;

        case HTTPInsufficientMemory:
            str = "HTTPInsufficientMemory";
            break;

        case HTTPSecurityAlertExtraneousResponseData:
            str = "HTTPSecurityAlertExtraneousResponseData";
            break;

        case HTTPSecurityAlertInvalidChunkHeader:
            str = "HTTPSecurityAlertInvalidChunkHeader";
            break;

        case HTTPSecurityAlertInvalidProtocolVersion:
            str = "HTTPSecurityAlertInvalidProtocolVersion";
            break;

        case HTTPSecurityAlertInvalidStatusCode:
            str = "HTTPSecurityAlertInvalidStatusCode";
            break;

        case HTTPSecurityAlertInvalidCharacter:
            str = "HTTPSecurityAlertInvalidCharacter";
            break;

        case HTTPSecurityAlertInvalidContentLength:
            str = "HTTPSecurityAlertInvalidContentLength";
            break;

        case HTTPParserPaused:
            str = "HTTPParserPaused";
            break;

        case HTTPParserInternalError:
            str = "HTTPParserInternalError";
            break;

        case HTTPHeaderNotFound:
            str = "HTTPHeaderNotFound";
            break;

        case HTTPInvalidResponse:
            str = "HTTPInvalidResponse";
            break;

        default:
            LogWarn( ( "Invalid status code received for string conversion: "
                       "StatusCode=%d", ( int ) status ) );
            break;
    }

    return str;
}

/*-----------------------------------------------------------*/

// === test/cbmc/include/transport_interface_stubs.h (CBMC include, verbatim from upstream) ===
/*
 * coreHTTP
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file transport_interface_stubs.h
 * @brief Functions, for CBMC proofs, to mock transport sending and receiving
 * implementations.
 */

#ifndef TRANSPORT_INTERFACE_STUBS_H_
#define TRANSPORT_INTERFACE_STUBS_H_

#include <stdint.h>

#ifndef MAX_TRIES
    #define MAX_TRIES    5
#endif

/**
 * @brief Transport interface stub for mocking data sent over the network.
 *
 * @param[in] pNetworkContext Implementation-defined network context.
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToSend Number of bytes to send over the network.
 *
 * @return The number of bytes sent or a negative error code.
 */
int32_t TransportInterfaceSendStub( NetworkContext_t * pNetworkContext,
                                    void * pBuffer,
                                    size_t bytesToSend );

/**
 * @brief Transport interface for mocking data received over the network.
 *
 * @param[in] pNetworkContext Implementation-defined network context.
 * @param[in] pBuffer Buffer to receive the data into.
 * @param[in] bytesToRecv Number of bytes requested from the network.
 *
 * @return The number of bytes received or a negative error code.
 */
int32_t TransportInterfaceReceiveStub( NetworkContext_t * pNetworkContext,
                                       void * pBuffer,
                                       size_t bytesToRecv );

#endif /* ifndef TRANSPORT_INTERFACE_STUBS_H_ */

// === test/cbmc/include/callback_stubs.h (CBMC include, verbatim from upstream) ===
/*
 * coreHTTP
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file callback_stubs.h
 * @brief Defines a stub function for
 * #HTTPClient_ResponseHeaderParsingCallback_t.onHeaderCallback
 */

#ifndef CALLBACK_STUBS_H_
#define CALLBACK_STUBS_H_

#include <string.h>
#include <stdint.h>


/**
 * @brief Invoked when both a header field and its associated header value are found.
 *
 * @param[in] pContext User context.
 * @param[in] fieldLoc Location of the header field name in the response buffer.
 * @param[in] fieldLen Length in bytes of the field name.
 * @param[in] valueLoc Location of the header value in the response buffer.
 * @param[in] valueLen Length in bytes of the value.
 * @param[in] statusCode The HTTP response status-code.
 */
void onHeaderCallbackStub( void * pContext,
                           const char * fieldLoc,
                           size_t fieldLen,
                           const char * valueLoc,
                           size_t valueLen,
                           uint16_t statusCode );

#endif /* ifndef CALLBACK_STUBS_H_ */

// === test/cbmc/include/get_time_stub.h (CBMC include, verbatim from upstream) ===
/*
 * coreHTTP
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file get_time_stub.h
 * @brief Stub definition for the application defined callback to retrieve the
 * current time in milliseconds.
 */
#ifndef GET_TIME_STUB_H_
#define GET_TIME_STUB_H_

/**
 * Application defined callback to retrieve the current time in milliseconds.
 *
 * @return The current time in milliseconds.
 */
uint32_t GetCurrentTimeStub( void );

#endif /* ifndef GET_TIME_STUB_H_ */

// === test/cbmc/include/http_cbmc_state.h (CBMC include, verbatim from upstream) ===
/*
 * coreHTTP
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file http_cbmc_state.h
 * @brief Functions to allocate memory and validate data types for proofs.
 */

#ifndef HTTP_CBMC_STATE_H_
#define HTTP_CBMC_STATE_H_

#include <stdbool.h>
#include <stdint.h>




struct NetworkContext
{
    int filler;
};

/**
 * @brief Attains coverage when a variable needs to possibly contain two values.
 */
bool nondet_bool();

/**
 * @brief Calls malloc based on given size or returns NULL for coverage.
 *
 * Implementation of safe malloc which returns NULL if the requested size is 0.
 * The behavior of malloc(0) is platform dependent.
 * It is possible for malloc(0) to return an address without allocating memory.
 *
 * @param[in] size Requested size to malloc.
 *
 * @return Requested memory or NULL.
 */
void * mallocCanFail( size_t size );

/**
 * @brief Allocates an #HTTPRequestHeaders_t object.
 *
 * @param[in] pRequestHeaders #HTTPRequestHeaders_t object to allocate.
 *
 * @return NULL or pointer to allocated #HTTPRequestHeaders_t object.
 */
HTTPRequestHeaders_t * allocateHttpRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders );

/**
 * @brief Validates if a #HTTPRequestHeaders_t object is feasible.
 *
 * @param[in] pRequestHeaders #HTTPRequestHeaders_t object to validate.
 *
 * @return True if #pRequestHeaders is feasible; false otherwise.
 */
bool isValidHttpRequestHeaders( const HTTPRequestHeaders_t * pRequestHeaders );

/**
 * @brief Allocates a #HTTPRequestInfo_t object.
 *
 * @param[in] pRequestInfo #HTTPRequestInfo_t object to allocate.
 *
 * @return NULL or pointer to allocated #HTTPRequestInfo_t object.
 */
HTTPRequestInfo_t * allocateHttpRequestInfo( HTTPRequestInfo_t * pRequestInfo );

/**
 * @brief Validates if a #HTTPRequestInfo_t object is feasible.
 *
 * @param[in] pRequestInfo #HTTPRequestInfo_t object to validate.
 *
 * @return True if #pRequestInfo is feasible; false otherwise.
 */
bool isValidHttpRequestInfo( const HTTPRequestInfo_t * pRequestInfo );

/**
 * @brief Allocates a #HTTPResponse_t object.
 *
 * @param[in] pResponse #HTTPResponse_t object to allocate.
 *
 * @return NULL or pointer to allocated #HTTPResponse_t object.
 */
HTTPResponse_t * allocateHttpResponse( HTTPResponse_t * pResponse );

/**
 * @brief Validates if a #HTTPResponse_t object is feasible.
 *
 * @param[in] pResponse #HTTPResponse_t object to validate.
 *
 * @return True if #HTTPResponse_t is feasible; false otherwise.
 */
bool isValidHttpResponse( const HTTPResponse_t * pResponse );

/**
 * @brief Allocates a #TransportInterface_t object.
 *
 * @param[in] pTransport #TransportInterface_t object to allocate.
 *
 * @return NULL or pointer to allocated #TransportInterface_t object.
 */
TransportInterface_t * allocateTransportInterface( TransportInterface_t * pTransport );

/**
 * @brief Validates if a #TransportInterface_t object is feasible.
 *
 * @param[in] pTransportInterface #TransportInterface_t object to validate.
 *
 * @return True if #pTransportInterface is feasible; false otherwise.
 */
bool isValidTransportInterface( TransportInterface_t * pTransportInterface );

/**
 * @brief Allocate an #llhttp_t object that is valid in the context of the
 * HTTPClient_Send() function.
 *
 * @param[in] pHttpParser #llhttp_t object to allocate.
 *
 * @return NULL or pointer to allocated #llhttp_t object.
 */
llhttp_t * allocateHttpSendParser( llhttp_t * pHttpParser );

/**
 * @brief Allocate an #HTTPParsingContext_t object.
 *
 * @param[in] pHttpParsingContext #HTTPParsingContext_t object to allocate.
 *
 * @return NULL or pointer to allocated #HTTPParsingContext_t object.
 */
HTTPParsingContext_t * allocateHttpSendParsingContext( HTTPParsingContext_t * pHttpParsingContext );

/**
 * @brief Validates if a #HTTPParsingContext_t object is feasible.
 *
 * @param[in] pHttpParsingContext #HTTPParsingContext_t object to validate.
 *
 * @return True if #pHttpParsingContext is feasible; false otherwise.
 */
bool isValidHttpSendParsingContext( const HTTPParsingContext_t * pHttpParsingContext );

/**
 * @brief Allocate an #llhttp_t object that is valid in the context of the
 * HTTPClient_ReadHeader() function.
 *
 * @param[in] pHttpParser #llhttp_t object to allocate.
 *
 * @return NULL or pointer to allocated #llhttp_t object.
 */
llhttp_t * allocateHttpReadHeaderParser( llhttp_t * pHttpParser );

/**
 * @brief Allocate an #findHeaderContext_t object.
 *
 * @param[in] pFindHeaderContext #findHeaderContext_t object to allocate.
 *
 * @return NULL or pointer to allocated #findHeaderContext_t object.
 */
findHeaderContext_t * allocateFindHeaderContext( findHeaderContext_t * pFindHeaderContext );


#endif /* ifndef HTTP_CBMC_STATE_H_ */


// === Harness body, folded into main() ===
/*
 * coreHTTP
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file HTTPClient_AddRangeHeader_harness.c
 * @brief Implements the proof harness for HTTPClient_AddRangeHeader function.
 */



char * httpHeaderStrncpy( char * pDest,
                          const char * pSrc,
                          size_t len,
                          uint8_t isField );

char * __CPROVER_file_local_core_http_client_c_httpHeaderStrncpy( char * pDest,
                                                                  const char * pSrc,
                                                                  size_t len,
                                                                  uint8_t isField )
{
    return httpHeaderStrncpy( pDest, pSrc, len, isField );
}

int main(void) {
    HTTPRequestHeaders_t * pRequestHeaders;
    int32_t rangeStartOrlastNbytes;
    int32_t rangeEnd;

    /* Initialize and make assumptions for request headers. */
    pRequestHeaders = allocateHttpRequestHeaders( NULL );
    __CPROVER_assume( isValidHttpRequestHeaders( pRequestHeaders ) );

    HTTPClient_AddRangeHeader( pRequestHeaders, rangeStartOrlastNbytes, rangeEnd );
    return 0;
}
