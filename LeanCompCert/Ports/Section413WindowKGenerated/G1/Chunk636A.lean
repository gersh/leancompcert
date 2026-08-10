import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk636A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362469132151703960, 362469191733049293⟩, ⟨1028995216243255394, 1031554704590699448⟩, true⟩

def state01 : KState := ⟨⟨362474994168252571, 362475053768860715⟩, ⟨656214104293396234, 658774817857249226⟩, true⟩

def words00 : List Nat := [371285410893091777, 371285410887616859, 371285410751980831, 371285410595887345, 371285410438990643, 371285410357905845, 371285410193466375, 371285410236519663, 371285410238172046, 371285410235105917]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 63600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 63600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362503742627927323, 362503802248065121⟩, ⟨(-1172626646852416490), (-1170064690911113524)⟩, true⟩

def words01 : List Nat := [371285410158213687, 371285410245258726, 371285410457242569, 371285410459410630, 371285410418537398, 371285410340550133, 371285410428430354, 371285410495012276, 371285410785566881, 371285411077053803]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 63610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 63600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492249698079895, 362492309337769217⟩, ⟨(-441452127659874125), (-438888927752235733)⟩, true⟩

def words02 : List Nat := [371285411368841290, 371285411425919909, 371285411551086131, 371285411677379663, 371285411877351086, 371285411879515634, 371285411812860878, 371285411733744866, 371285411819476941, 371285411930408776]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 63620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 63600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362465628263879602, 362465687923043020⟩, ⟨1252649033153902480, 1255213472298346494⟩, true⟩

def words03 : List Nat := [371285412147538750, 371285412365563874, 371285412582028440, 371285412584191278, 371285412471427947, 371285412345443023, 371285412218390647, 371285412193994755, 371285411886591772, 371285411579113076]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 63630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 63600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490576542189792, 362490636220741938⟩, ⟨(-335183886787205713), (-332618213650745019)⟩, true⟩

def words04 : List Nat := [371285411270662064, 371285411140786176, 371285410887024551, 371285410838498771, 371285410789280358, 371285410702804109, 371285410400333223, 371285410346062750, 371285410480652803, 371285410564999676]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 63640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 63600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk636A
