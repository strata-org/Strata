/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.B3.DDMFormatDeclarationsTests
import Strata.Languages.B3.DDMTransform.Conversion

/-!
# B3 Program Formatting Tests

Tests for round-trip conversion and formatting of complete B3 programs.
Verifies that DDM AST → B3 AST → B3 CST → formatted output preserves structure and catches conversion errors.
-/

namespace B3

open Std (Format)
open Strata
open Strata.B3CST

def roundtripProgram (p : Program) : Format :=
  let ctx := FormatContext.ofDialects p.dialects p.globalContext {}
  let state : FormatState := { openDialects := p.dialects.toList.foldl (init := {}) fun a d => a.insert d.name }
  match p.commands.toList with
  | [op] =>
    if op.name.name == "command_program" then
      match op.args.toList with
      | [ArgF.op prog] => doRoundtripProgram prog ctx state false
      | _ => "Error: expected program op"
    else s!"Error: expected command_program, got {op.name.name}"
  | _ => "Error: expected single command"

section ProgramRoundtripTests

-- Type declaration
/--
info: <B3 omitted>
CST→AST Errors:
  Unresolved identifier '«myFileSystemName: string»'
  Unresolved identifier '«BlockPublicAcls: string»'
  Unresolved identifier '«bucket: string»'
  Unresolved identifier '«is-blocked: string»'
  Unresolved identifier '«bucket: string»'
  Unresolved identifier '«is-not-blocked: string»'
AST→CST Errors:
  Variable index @2 is out of bounds (context has 2 variables)
  Variable index @12 is out of bounds (context has 12 variables)
  Variable index @12 is out of bounds (context has 12 variables)
  Variable index @12 is out of bounds (context has 12 variables)
  Variable index @12 is out of bounds (context has 12 variables)
  Variable index @12 is out of bounds (context has 12 variables)
---
info:
procedure Good(out result : XResult)
{
  var cresult : CResult
  CreateClient(|@2|, out cresult)
  if !CIsSuccess(cresult) ⏎
    {
      result := XFailure(CFailure..msg(cresult))
      return
    }
  var fileSystem := CSuccess..value(cresult)
  var aresult : AResult
  ListBuckets(fileSystem, out aresult)
  if !AIsSuccess(aresult) ⏎
    {
      result := XFailure(AFailure..msg(aresult))
      return
    }
  var aresponse := ASuccess..value(aresult)
  var buckets := AResponse..buckets(aresponse)
  var i := 0
  loop
    invariant 0 <= i && i <= length(buckets) ⏎
  {
    if i == length(buckets) ⏎
      {
        exit ⏎
      }
    check 0 <= i && i < length(buckets)
    var bucket := select(buckets, i)
    var bucketName := Bucket..name(bucket)
    var bresult : BResult
    GetPublicAccessBlock(fileSystem, bucketName, out bresult)
    if !BIsSuccess(bresult) ⏎
      {
        result := XFailure(BFailure..msg(bresult))
        return
      }
    var bresponse := BSuccess..value(bresult)
    var isBlocked := GetAttributeValue(BResponse..getConfig(bresponse), |@12|)
    if isBlocked ⏎
      {
        Print(|@12|, bucketName, |@12|)
      }
    else ⏎
      {
        Print(|@12|, bucketName, |@12|)
      }
    i := i + 1
  }
  var x : X
  result := XSuccess(x)
}
procedure CreateClient(name : string, out result : CResult)
function UserOwnsBucket(name : string) : bool
type Client
procedure ListBuckets(c : Client, out aresult : AResult)
  ensures AIsSuccess(aresult) ==> (forall bucket : Bucket pattern Bucket..name(bucket) pattern in(bucket, AResponse..buckets(ASuccess..value(aresult))) in(bucket, AResponse..buckets(ASuccess..value(aresult))) ==> UserOwnsBucket(Bucket..name(bucket)))
procedure GetPublicAccessBlock(c : Client, Bucket : string, out result : BResult)
  requires UserOwnsBucket(Bucket)
type AResponse
function AResponse(injective buckets : BucketSeq) : AResponse
type BResponse
function BResponse(injective getConfig : BlockConfig) : BResponse
type Bucket
function Bucket(injective name : string) : Bucket
type BlockConfig
function GetAttributeValue(config : BlockConfig, attribute : string) : bool
type X
type XResult
tagger XResultTag for XResult
function XSuccess(injective value : X) : XResult tag XResultTag
function XFailure(injective msg : string) : XResult tag XResultTag
function XIsSuccess(r : XResult) : bool {
  XResultTag(r) == XSuccess..tag()
}
type CResult
tagger CResultTag for CResult
function CSuccess(injective value : Client) : CResult tag CResultTag
function CFailure(injective msg : string) : CResult tag CResultTag
function CIsSuccess(r : CResult) : bool {
  CResultTag(r) == CSuccess..tag()
}
type AResult
tagger AResultTag for AResult
function ASuccess(injective value : AResponse) : AResult tag AResultTag
function AFailure(injective msg : string) : AResult tag AResultTag
function AIsSuccess(r : AResult) : bool {
  AResultTag(r) == ASuccess..tag()
}
type BResult
tagger BResultTag for BResult
function BSuccess(injective value : BResponse) : BResult tag BResultTag
function BFailure(injective msg : string) : BResult tag BResultTag
function BIsSuccess(r : BResult) : bool {
  BResultTag(r) == BSuccess..tag()
}
type BucketSeq
function select(s : BucketSeq, i : int) : Bucket
function length(s : BucketSeq) : int
axiom explains length
  forall s : BucketSeq pattern length(s) 0 <= length(s)
function in(b : Bucket, s : BucketSeq) : bool {
  exists i : int pattern select(s, i) 0 <= i && i < length(s) && select(s, i) == b
}
type string
procedure Print(a : string, b : string, c : string)
-/
#guard_msgs in
#eval roundtripProgram $ #strata program B3CST;
// This example program shows many B3 features in use. The main point is to prove
// that GetPublicAccessBlock is called with a bucket name that satisfies UserOwnsBucket.
// This properties is guaranteed by the postcondition of ListBuckets, which, upon
// success, returns a sequence where every bucket name satisfies GetPublicAccessBlock.
//
// Here is the program shown in the syntax of a Dafny-like programming-language:
//
//     var fileSystem :- CreateClient("myFileSystemName")
//     var aresponse :- fileSystem.ListBuckets()
//     var buckets := aresponse.buckets
//     for i := 0 to |buckets| {
//       var bucket := buckets[i]
//       var bucketName := bucket.name
//       var bresponse :- fileSystem.GetPublicAccessBlock(bucketName)
//       var isBlocked := bresponse.getConfig.GetAttributeValue("BlockPublicAcls")
//       if isBlocked {
//         print "bucket", bucketName, "is blocked"
//       } else {
//         print "bucket", bucketName, "is not blocked"
//       }
//      }
//
// Note that B3 identifiers may contain "." characters. B3 uses ".." as part of the
// name when it generates functions (for example, the function names generated as a result
// of declaring a parameter to be "injective").

procedure Good(out result: XResult) {
  var cresult: CResult
  CreateClient(|myFileSystemName: string|, out cresult)
  if !CIsSuccess(cresult) {
    result := XFailure(CFailure..msg(cresult))
    return
  }
  var fileSystem := CSuccess..value(cresult)

  var aresult: AResult
  ListBuckets(fileSystem, out aresult)
  if !AIsSuccess(aresult) {
    result := XFailure(AFailure..msg(aresult))
    return
  }
  var aresponse := ASuccess..value(aresult)

  var buckets := AResponse..buckets(aresponse)

  var i := 0
  loop
    invariant 0 <= i && i <= length(buckets)
  {
    if i == length(buckets) {
      exit
    }

    check 0 <= i && i < length(buckets)
    var bucket := select(buckets, i)

    var bucketName := Bucket..name(bucket)

    var bresult: BResult
    GetPublicAccessBlock(fileSystem, bucketName, out bresult)
    if !BIsSuccess(bresult) {
      result := XFailure(BFailure..msg(bresult))
      return
    }
    var bresponse := BSuccess..value(bresult)

    var isBlocked := GetAttributeValue(BResponse..getConfig(bresponse), |BlockPublicAcls: string|)

    if isBlocked {
      Print(|bucket: string|, bucketName, |is-blocked: string|)
    } else {
      Print(|bucket: string|, bucketName, |is-not-blocked: string|)
    }

    i := i + 1
  }

  var x: X
  result := XSuccess(x)
}

// --------------------------------------------------------------------

// The file-system API is the following:

procedure CreateClient(name: string, out result: CResult)

// This predicate says whether or not the given bucket name is owned by the user.
// It is used in the postcondition of ListBuckets and in the precondition of
// GetPublicAccessBlock.
function UserOwnsBucket(name: string): bool

type Client

procedure ListBuckets(c: Client, out aresult: AResult)
  ensures AIsSuccess(aresult) ==>
    forall bucket: Bucket
      pattern Bucket..name(bucket)
      pattern in(bucket, AResponse..buckets(ASuccess..value(aresult)))
      in(bucket, AResponse..buckets(ASuccess..value(aresult))) ==>
      UserOwnsBucket(Bucket..name(bucket))

procedure GetPublicAccessBlock(c: Client, Bucket: string, out result: BResult)
  requires UserOwnsBucket(Bucket)

// --------------------------------------------------------------------

// The example program uses an API model where each API entry point returns a "response".
// This is typical in many code bases, for example in Java, because it allows the API
// to evolve to add more attributes of the response in the future. What that means for
// the example program is that there are different response types. Here, those are modeled
// as records with one just field.

// datatype AResponse = AResponse(buckets: BucketSeq)
type AResponse
function AResponse(injective buckets: BucketSeq): AResponse

// datatype BResponse = BResponse(getConfig: BlockConfig)
type BResponse
function BResponse(injective getConfig: BlockConfig): BResponse

// --------------------------------------------------------------------

// For the purpose of the example, a bucket is something that has a name. In a full API,
// buckets would also have some data, of course.

// datatype Bucket = Bucket(name: string)
type Bucket
function Bucket(injective name: string): Bucket

// --------------------------------------------------------------------

// In the example, a block configuration is a set of named attributes, each of which can
// be false or true.

type BlockConfig

function GetAttributeValue(config: BlockConfig, attribute: string): bool

// --------------------------------------------------------------------

// The example program is written in the style of Rust, Go, and Dafny, where a failure
// is reported as a special return value that have to be tested by the caller. In Go,
// such querying and propagation of failures is done manually, whereas Rust has the
// "?" operator and Dafny has the ":-" operator for doing this. Such code is translated
// into B3 by doing the checking explicitly.
//
// Using datatypes with type parameters, such Result types can be defined as
//
//     datatype Result<X> = Success(value: X) | Failure(msg: string)
//
// Since B3 does not support polymorphism, there is one Result type for each success
// type.

type X
type XResult // Result<()>
tagger XResultTag for XResult
function XSuccess(injective value: X): XResult tag XResultTag
function XFailure(injective msg: string): XResult tag XResultTag
function XIsSuccess(r: XResult): bool {
  XResultTag(r) == XSuccess..tag()
}

type CResult // Result<Client>
tagger CResultTag for CResult
function CSuccess(injective value: Client): CResult tag CResultTag
function CFailure(injective msg: string): CResult tag CResultTag
function CIsSuccess(r: CResult): bool {
  CResultTag(r) == CSuccess..tag()
}

type AResult // Result<AResponse>
tagger AResultTag for AResult
function ASuccess(injective value: AResponse): AResult tag AResultTag
function AFailure(injective msg: string): AResult tag AResultTag
function AIsSuccess(r: AResult): bool {
  AResultTag(r) == ASuccess..tag()
}

type BResult // Result<BResponse>
tagger BResultTag for BResult
function BSuccess(injective value: BResponse): BResult tag BResultTag
function BFailure(injective msg: string): BResult tag BResultTag
function BIsSuccess(r: BResult): bool {
  BResultTag(r) == BSuccess..tag()
}

// --------------------------------------------------------------------

// Finally, we have a type BucketSeq that models a sequence of buckets
// and a(n uninterpreted) string type whose values can be printed.
//
// In a source programming language, the "select" operation on a sequence
// has a precondition that the given index is in range. The example B3 code
// above uses a "check" statement to enforce that precondition.

type BucketSeq

function select(s: BucketSeq, i: int): Bucket

function length(s: BucketSeq): int

axiom explains length
  forall s: BucketSeq
    pattern length(s)
    0 <= length(s)

function in(b: Bucket, s: BucketSeq): bool {
  exists i: int
    pattern select(s, i)
    0 <= i && i < length(s) && select(s, i) == b
}

type string

procedure Print(a: string, b: string, c: string)
#end

end ProgramRoundtripTests

end B3
