import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk614A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk614B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk614A

def state06 : KState := ⟨⟨360572880590659368, 360572904684783421⟩, ⟨591291948196580843, 592292319181968721⟩, true⟩

def words05 : List Nat := [360582543252556144, 360582543396280743, 360582543532483554, 360582543533344898, 360582543405839028, 360582543020452127, 360582542634916564, 360582542190642770, 360582541878089958, 360582541722192825]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 61450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 61400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360567582483761195, 360567606586092188⟩, ⟨916807425373968530, 917808300798396628⟩, true⟩

def words06 : List Nat := [360582541566168098, 360582541277678956, 360582540797394150, 360582540581906076, 360582540366193771, 360582540027762438, 360582539501499221, 360582538773397882, 360582538045149280, 360582537581712790]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 61460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 61400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552034761406134, 360552058871850783⟩, ⟨1872727078121900113, 1873728452332501943⟩, true⟩

def words07 : List Nat := [360582537361111946, 360582537383572839, 360582537384340929, 360582537262831935, 360582537148015052, 360582536966794505, 360582536785330017, 360582536681860098, 360582536407227648, 360582535912389699]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 61470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 61400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587161155063301, 360587185273656191⟩, ⟨(-287080164683107397), (-286078289478904211)⟩, true⟩

def words08 : List Nat := [360582535417383676, 360582534915367422, 360582534544837399, 360582534438867169, 360582534332831316, 360582534003492388, 360582533491336169, 360582533243835424, 360582532996066166, 360582532913319249]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 61480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 61400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586397069932268, 360586421196716395⟩, ⟨(-240084177938758160), (-239081799015075300)⟩, true⟩

def words09 : List Nat := [360582532914087010, 360582532847901420, 360582532978825134, 360582533349607157, 360582533530235377, 360582533710985728, 360582533759389847, 360582533760251927, 360582533686804718, 360582533750999821]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 61490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 61400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 61400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk614B
