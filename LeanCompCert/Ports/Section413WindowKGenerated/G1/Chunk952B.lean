import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk952A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk952B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk952A

def state06 : KState := ⟨⟨362472350868633179, 362472488786502742⟩, ⟨1203102997037273999, 1211973324340802845⟩, true⟩

def words05 : List Nat := [371285212136982600, 371285212143465458, 371285212148512437, 371285212151851485, 371285212021645043, 371285211926374928, 371285211840160408, 371285211843499296, 371285211709980379, 371285211580165778]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486610563646783, 362486748511433799⟩, ⟨(-155341416527778165), (-146468239136155821)⟩, true⟩

def words06 : List Nat := [371285211448872330, 371285211429327140, 371285211353492416, 371285211318184881, 371285211281799929, 371285211231684505, 371285211094623880, 371285211069592985, 371285211106434657, 371285211126089506]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486866352438686, 362487004330655832⟩, ⟨(-179701816451640000), (-170825739826052586)⟩, true⟩

def words07 : List Nat := [371285211128602101, 371285211128646137, 371285211233996371, 371285211298039872, 371285211375478373, 371285211454160999, 371285211512125470, 371285211515465223, 371285211445070457, 371285211468072253]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487613994742663, 362487752002701825⟩, ⟨(-250918456852639833), (-242039546254942655)⟩, true⟩

def words08 : List Nat := [371285211587854244, 371285211626942461, 371285211664433769, 371285211703061747, 371285211735138393, 371285211738819558, 371285211801028382, 371285211889790743, 371285211968308236, 371285211998438517]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502065059212296, 362502203097362278⟩, ⟨(-1628061470599554380), (-1619179682964435470)⟩, true⟩

def words09 : List Nat := [371285212072924860, 371285212149104261, 371285212279495152, 371285212319394993, 371285212341783786, 371285212365261004, 371285212487019949, 371285212570137989, 371285212750687633, 371285212932694915]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk952B
