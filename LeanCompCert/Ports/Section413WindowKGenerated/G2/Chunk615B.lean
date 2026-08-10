import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk615A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk615B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk615A

def state06 : KState := ⟨⟨360591697241934986, 360591721417710298⟩, ⟨(-566179389709694844), (-565173996359144540)⟩, true⟩

def words05 : List Nat := [360582540520795400, 360582540347227275, 360582540262859676, 360582540484424408, 360582540560624997, 360582540636966420, 360582540637737318, 360582540517346808, 360582540552575482, 360582540702706333]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 61550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 61500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577777247521664, 360577801431416859⟩, ⟨290798076263723939, 291803969515748081⟩, true⟩

def words06 : List Nat := [360582541116268835, 360582541267270546, 360582541285672760, 360582541304168756, 360582541304903557, 360582541144752309, 360582541138114398, 360582541075101484, 360582541011998892, 360582540816986386]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 61560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 61500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597311280734054, 360597335472789221⟩, ⟨(-912004989485715024), (-910998593784049390)⟩, true⟩

def words07 : List Nat := [360582540785715124, 360582540831685516, 360582541062813397, 360582541205921131, 360582541206717931, 360582541121410696, 360582541161702357, 360582541489570418, 360582541730522028, 360582541971647895]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 61570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 61500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600688655841420, 360600712856111602⟩, ⟨(-1120103680626766529), (-1119096779003162981)⟩, true⟩

def words08 : List Nat := [360582542046188739, 360582542047052520, 360582542154046700, 360582542339916734, 360582542439139898, 360582542608736627, 360582542644746867, 360582542680842587, 360582542749931228, 360582543045928245]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 61580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 61500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583781779546581, 360583805987965768⟩, ⟨(-78690570550179322), (-77683166989346088)⟩, true⟩

def words09 : List Nat := [360582543430813804, 360582543815850522, 360582543992549844, 360582544224832358, 360582544338290769, 360582544451984218, 360582544721726791, 360582544875434183, 360582544896675946, 360582544918064479]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 61590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 61500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 61500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk615B
