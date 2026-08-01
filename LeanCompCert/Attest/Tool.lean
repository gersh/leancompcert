import LeanCompCert.Attest.Receipt

/-!
# Producing and checking receipts, out of band

The `IO` half of the receipt standard: key generation, signing, verification,
and the on-disk format.  **Nothing here is a proof and nothing here is
trusted.**  A receipt this module writes is checked in Lean by
`Attest.receiptBinds`, which re-derives the program digest from the emitted C
and re-checks the signature with the consumer's own verifier.  If this tool is
wrong, the Lean check fails; it cannot make a bad receipt pass.

The one property that *is* structural: `renderReceipt` and `parseReceipt` are
written against `RunReceipt.payload`, the same function the kernel check uses.
The signed bytes are literally a prefix of the receipt file, so there is no
second serialisation to drift out of step with the first.

## The on-disk format

A receipt file is the signed payload followed by the signature:

```text
leancompcert-receipt/1     ← 16 payload lines, in RunReceipt.payload order
local-signature
straight-line
…
04a1b2…                    ← public key (last payload line)
865ad0…                    ← signature, r ‖ s, 128 lowercase hex
```

Line-oriented rather than JSON on purpose: every field is constrained to a
digest, a bounded label, a decimal integer or an enumeration label, none of
which can contain a newline, so the encoding needs no escaping and the bytes
under signature are exactly the file's first sixteen lines.

## Cryptography

Delegated to `openssl` — this tool does no arithmetic of its own.  OpenSSL
speaks DER for both keys and signatures while the receipt format uses SEC1
uncompressed points and fixed-width `r ‖ s`, so the conversions are here.  They
are pure byte surgery over fixed structures and are exercised by the round-trip
test in `LeanCompCertTests`.
-/

namespace LeanCompCert.Attest.Tool

/-! ## Hex and byte helpers -/

private def hexDigits : Array Char :=
  #['0', '1', '2', '3', '4', '5', '6', '7',
    '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

def toHex (bytes : ByteArray) : String :=
  bytes.foldl (init := "") fun acc b =>
    acc.push (hexDigits[(b.toNat >>> 4)]!) |>.push (hexDigits[(b.toNat &&& 15)]!)

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def ofHex (s : String) : Option ByteArray := do
  let chars := s.toList
  if chars.length % 2 != 0 then none else
  let rec go : List Char → ByteArray → Option ByteArray
    | [], acc => some acc
    | hi :: lo :: rest, acc => do
        let h ← hexValue hi
        let l ← hexValue lo
        go rest (acc.push (UInt8.ofNat (h * 16 + l)))
    | _, _ => none
  go chars ByteArray.empty

/-! ## DER ↔ wire conversions

Two fixed structures, both small.

* An `id-ecPublicKey`/`prime256v1` `SubjectPublicKeyInfo` is a constant 26-byte
  prefix followed by the 65-byte uncompressed point, so the conversion is a
  concatenation in one direction and a suffix in the other.
* An ECDSA signature is `SEQUENCE { INTEGER r, INTEGER s }` with minimal-length
  big-endian integers — which means a leading `00` when the high bit is set,
  and no leading zeros otherwise.  Getting that wrong produces a DER blob
  OpenSSL rejects, so the failure is loud. -/

/-- The DER `SubjectPublicKeyInfo` prefix for an uncompressed P-256 key. -/
def p256SpkiPrefix : ByteArray :=
  match ofHex "3059301306072a8648ce3d020106082a8648ce3d030107034200" with
  | some bytes => bytes
  | none => ByteArray.empty

/-- SEC1 uncompressed point hex → DER `SubjectPublicKeyInfo`. -/
def publicKeyDerOfHex (pointHex : String) : Option ByteArray := do
  if pointHex.length != 130 then none else
  let point ← ofHex pointHex
  if point.size != 65 || point[0]! != 4 then none else
  some (p256SpkiPrefix ++ point)

/-- DER `SubjectPublicKeyInfo` → SEC1 uncompressed point hex. -/
def publicKeyHexOfDer (der : ByteArray) : Option String :=
  if der.size < 65 then none else
  let point := der.extract (der.size - 65) der.size
  if point[0]! != 4 then none else some (toHex point)

/-- Strip leading zero bytes, keeping at least one byte. -/
private def trimLeadingZeros (bytes : List UInt8) : List UInt8 :=
  match bytes with
  | [] => [0]
  | b :: rest => if b == 0 && !rest.isEmpty then trimLeadingZeros rest else b :: rest

/-- A minimal-length DER INTEGER body for a non-negative big-endian value. -/
private def derIntegerBody (bytes : List UInt8) : List UInt8 :=
  let trimmed := trimLeadingZeros bytes
  match trimmed with
  | b :: _ => if b ≥ 128 then 0 :: trimmed else trimmed
  | [] => [0]

/-- Fixed-width `r ‖ s` hex → DER `SEQUENCE { INTEGER, INTEGER }`. -/
def signatureDerOfHex (rawHex : String) : Option ByteArray := do
  if rawHex.length != 128 then none else
  let raw ← ofHex rawHex
  if raw.size != 64 then none else
  let r := derIntegerBody (raw.extract 0 32).toList
  let s := derIntegerBody (raw.extract 32 64).toList
  let body :=
    (2 :: UInt8.ofNat r.length :: r) ++ (2 :: UInt8.ofNat s.length :: s)
  if body.length > 127 then none else
  some (ByteArray.mk ⟨(48 : UInt8) :: UInt8.ofNat body.length :: body⟩)

private def leftPad32 (bytes : List UInt8) : Option (List UInt8) :=
  let trimmed := trimLeadingZeros bytes
  if trimmed.length > 32 then none
  else some (List.replicate (32 - trimmed.length) (0 : UInt8) ++ trimmed)

/-- DER `SEQUENCE { INTEGER, INTEGER }` → fixed-width `r ‖ s` hex. -/
def signatureHexOfDer (der : ByteArray) : Option String := do
  let bytes := der.toList
  match bytes with
  | 48 :: _len :: rest =>
      match rest with
      | 2 :: rlen :: tail =>
          let rl := rlen.toNat
          if tail.length < rl then none else
          let r := tail.take rl
          match tail.drop rl with
          | 2 :: slen :: stail =>
              let sl := slen.toNat
              if stail.length < sl then none else
              let s := stail.take sl
              let r32 ← leftPad32 r
              let s32 ← leftPad32 s
              some (toHex (ByteArray.mk ⟨r32 ++ s32⟩))
          | _ => none
      | _ => none
  | _ => none

/-! ## Shelling out -/

private def runProcess (cmd : String) (args : Array String) :
    IO (Except String String) := do
  try
    let out ← IO.Process.output { cmd, args }
    if out.exitCode == 0 then
      return .ok out.stdout
    return .error s!"{cmd} exited {out.exitCode}: {out.stderr.trimAscii}"
  catch e =>
    return .error s!"{cmd} could not be run: {e}"

/-- SHA-256 of a string's UTF-8 bytes, as 64 lowercase hex characters.

Goes through a file rather than a pipe so the bytes written are exactly the
bytes hashed, with no shell quoting in the way. -/
def sha256Hex (scratch : System.FilePath) (text : String) :
    IO (Except String String) := do
  IO.FS.createDirAll scratch
  let path := scratch / "digest-input"
  IO.FS.writeFile path text
  match ← runProcess "sha256sum" #[path.toString] with
  | .error message => return .error message
  | .ok out =>
      let digest := ((out.splitOn " ").headD "").trimAscii.toString
      if digest.length == 64 then return .ok digest
      return .error s!"sha256sum produced an unexpected line: {out}"

/-- A fresh 256-bit nonce. -/
def freshNonce : IO (Except String String) := do
  match ← runProcess "openssl" #["rand", "-hex", "32"] with
  | .error message => return .error message
  | .ok out =>
      let nonce := out.trimAscii.toString
      if nonce.length == 64 then return .ok nonce
      return .error s!"openssl rand produced an unexpected value: {out}"

/-- An RFC 3339 UTC timestamp. -/
def utcNow : IO String := do
  match ← runProcess "date" #["-u", "+%Y-%m-%dT%H:%M:%SZ"] with
  | .error _ => return "unknown-time"
  | .ok out => return out.trimAscii.toString

/-! ## Keys -/

/-- Where a locally generated key lives by default.

⚠ This is a private key on the machine that runs the binaries.  A receipt it
signs is **tamper-evident, not attested**: anyone who can read this file can
sign any value.  See `LeanCompCert/Trusted/LocalReceipt.lean`. -/
def defaultKeyPath : System.FilePath := ".lake" / "build" / "attest" / "key.pem"

/-- Generate a P-256 signing key, refusing to overwrite an existing one. -/
def generateKey (path : System.FilePath) : IO (Except String String) := do
  if ← path.pathExists then
    return .error s!"{path} already exists; refusing to overwrite a signing key"
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  match ← runProcess "openssl"
      #["ecparam", "-name", "prime256v1", "-genkey", "-noout",
        "-out", path.toString] with
  | .error message => return .error message
  | .ok _ =>
      let _ ← runProcess "chmod" #["600", path.toString]
      return .ok s!"wrote {path}"

/-- The SEC1 uncompressed public point of a private key, as hex. -/
def publicKeyHex (path : System.FilePath) (scratch : System.FilePath) :
    IO (Except String String) := do
  IO.FS.createDirAll scratch
  let der := scratch / "pub.der"
  match ← runProcess "openssl"
      #["ec", "-in", path.toString, "-pubout", "-outform", "DER",
        "-out", der.toString] with
  | .error message => return .error message
  | .ok _ =>
      let bytes ← IO.FS.readBinFile der
      match publicKeyHexOfDer bytes with
      | some hex => return .ok hex
      | none => return .error "could not read an uncompressed P-256 point from the key"

/-- Sign a payload, returning the signature as fixed-width `r ‖ s` hex. -/
def signPayload (path : System.FilePath) (scratch : System.FilePath)
    (payload : String) : IO (Except String String) := do
  IO.FS.createDirAll scratch
  let payloadPath := scratch / "payload"
  let sigPath := scratch / "payload.sig.der"
  IO.FS.writeFile payloadPath payload
  match ← runProcess "openssl"
      #["dgst", "-sha256", "-sign", path.toString,
        "-out", sigPath.toString, payloadPath.toString] with
  | .error message => return .error message
  | .ok _ =>
      let der ← IO.FS.readBinFile sigPath
      match signatureHexOfDer der with
      | some hex => return .ok hex
      | none => return .error "openssl produced a signature this tool cannot re-encode"

/-- Check a signature over a payload.  Fail-closed: any error is `false`. -/
def verifySignature (scratch : System.FilePath) (publicKeyHex payload
    signatureHex : String) : IO Bool := do
  IO.FS.createDirAll scratch
  let some keyDer := publicKeyDerOfHex publicKeyHex | return false
  let some sigDer := signatureDerOfHex signatureHex | return false
  let keyPath := scratch / "verify-pub.der"
  let sigPath := scratch / "verify-sig.der"
  let payloadPath := scratch / "verify-payload"
  IO.FS.writeBinFile keyPath keyDer
  IO.FS.writeBinFile sigPath sigDer
  IO.FS.writeFile payloadPath payload
  match ← runProcess "openssl"
      #["dgst", "-sha256", "-verify", keyPath.toString, "-keyform", "DER",
        "-signature", sigPath.toString, payloadPath.toString] with
  | .error _ => return false
  | .ok out => return (out.trimAscii.toString == "Verified OK")

/-! ## The on-disk record -/

def renderReceipt (r : RunReceipt) : String :=
  r.payload ++ r.signature ++ "\n"

private def kindOfLabel : String → Option AttestationKind
  | "local-signature" => some .localSignature
  | "enclave-quote" => some .enclaveQuote
  | _ => none

private def verdictOfLabel : String → Option RunVerdict
  | "agrees" => some .agrees
  | "disagrees" => some .disagrees
  | "abnormal" => some .abnormal
  | _ => none

/-- Read a receipt file.  Fail-closed: a file with the wrong number of lines,
an unknown enumeration label or a non-integer value is refused rather than
patched up. -/
def parseReceipt (text : String) : Except String RunReceipt :=
  let lines := (text.splitOn "\n").filter (· != "")
  match lines with
  | [schema, kind, route, campaign, digestName, programHash, paramsHash,
      ccompVersion, binaryDigest, linkDescription, value, verdict, machine,
      nonce, recordedAt, publicKey, signature] => do
      let some attestation := kindOfLabel kind
        | .error s!"unknown attestation kind '{kind}'"
      let some verdict' := verdictOfLabel verdict
        | .error s!"unknown verdict '{verdict}'"
      let some value' := value.toInt?
        | .error s!"value '{value}' is not an integer"
      .ok {
        schema, attestation, routeLabel := route, campaign, digestName,
        programHash, paramsHash,
        toolchain := { ccompVersion, binaryDigest, linkDescription },
        value := value', verdict := verdict', machine, nonce, recordedAt,
        publicKey, signature }
  | _ =>
      .error
        s!"a receipt has exactly 17 non-empty lines; this one has {lines.length}"

private def leanKind : AttestationKind → String
  | .localSignature => ".localSignature"
  | .enclaveQuote => ".enclaveQuote"

private def leanVerdict : RunVerdict → String
  | .agrees => ".agrees"
  | .disagrees => ".disagrees"
  | .abnormal => ".abnormal"

/-- The receipt as a Lean term, for pasting into a certificate file.

The receipt is *data in the consumer's source*, exactly like the certified
constant: a reviewer reads it in the diff, and the kernel re-checks every
clause of `receiptBinds` against it. -/
def renderLean (name : String) (r : RunReceipt) : String :=
  "open LeanCompCert.Attest in\n" ++
  s!"def {name} : RunReceipt := \{\n" ++
  s!"  schema := \"{r.schema}\"\n" ++
  s!"  attestation := {leanKind r.attestation}\n" ++
  s!"  routeLabel := \"{r.routeLabel}\"\n" ++
  s!"  campaign := \"{r.campaign}\"\n" ++
  s!"  digestName := \"{r.digestName}\"\n" ++
  s!"  programHash := \"{r.programHash}\"\n" ++
  s!"  paramsHash := \"{r.paramsHash}\"\n" ++
  s!"  toolchain := \{\n" ++
  s!"    ccompVersion := \"{r.toolchain.ccompVersion}\"\n" ++
  s!"    binaryDigest := \"{r.toolchain.binaryDigest}\"\n" ++
  s!"    linkDescription := \"{r.toolchain.linkDescription}\" }\n" ++
  s!"  value := {r.value}\n" ++
  s!"  verdict := {leanVerdict r.verdict}\n" ++
  s!"  machine := \"{r.machine}\"\n" ++
  s!"  nonce := \"{r.nonce}\"\n" ++
  s!"  recordedAt := \"{r.recordedAt}\"\n" ++
  s!"  publicKey := \"{r.publicKey}\"\n" ++
  s!"  signature := \"{r.signature}\" }\n"

/-! ## The `verify-receipt` check

Everything `receiptBinds` checks that this tool *can* check without the
consumer's Lean crypto: the schema, the field shapes, the verdict, the program
digest against freshly re-emitted C, and the signature.  It deliberately does
**not** claim to be the authoritative check — that is `receiptBinds`, in the
kernel, with the consumer's own verifier. -/

structure VerifyOutcome where
  ok : Bool
  lines : List String

def verifyReceiptAgainst (scratch : System.FilePath) (r : RunReceipt)
    (emitted : Except (Array String) String) : IO VerifyOutcome := do
  let mut lines : List String := []
  let mut ok := true
  let note (good : Bool) (label : String) : String :=
    (if good then "  ok   " else "  FAIL ") ++ label
  if r.schema != schemaVersion then
    ok := false
    lines := lines ++ [note false s!"schema is '{r.schema}', expected '{schemaVersion}'"]
  else
    lines := lines ++ [note true s!"schema {r.schema}"]
  if r.verdict != RunVerdict.agrees then
    ok := false
    lines := lines ++ [note false s!"verdict is '{r.verdict.label}', not 'agrees'"]
  else
    lines := lines ++ [note true "verdict agrees"]
  if !isDigest256 r.programHash || !isDigest256 r.paramsHash
      || !isDigest256 r.nonce || !r.toolchain.wellFormed
      || !isP256PublicKey r.publicKey || !isP256Signature r.signature
      || !isLabel r.campaign || !isLabel r.machine || !isLabel r.recordedAt then
    ok := false
    lines := lines ++ [note false "field shapes (digests, key, signature, labels)"]
  else
    lines := lines ++ [note true "field shapes"]
  match emitted with
  | .error errors =>
      ok := false
      lines := lines ++
        [note false s!"could not re-emit the certificate's C: {errors.toList}"]
  | .ok source =>
      match ← sha256Hex scratch source with
      | .error message =>
          ok := false
          lines := lines ++ [note false s!"could not digest the emitted C: {message}"]
      | .ok digest =>
          if digest == r.programHash then
            lines := lines ++
              [note true s!"programHash matches freshly emitted C ({digest})"]
          else
            ok := false
            lines := lines ++
              [note false s!"programHash {r.programHash} ≠ digest of emitted C {digest}"]
  if ← verifySignature scratch r.publicKey r.payload r.signature then
    lines := lines ++ [note true s!"signature verifies under {r.publicKey.take 16}…"]
  else
    ok := false
    lines := lines ++ [note false "signature does NOT verify over the payload"]
  return ⟨ok, lines⟩

end LeanCompCert.Attest.Tool
