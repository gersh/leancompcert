import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk250A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk250B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk250A

def state06 : KState := ⟨⟨360584820268689286, 360584823987428720⟩, ⟨(-23950114344177157), (-23887071101661709)⟩, true⟩

def words05 : List Nat := [360583871380876388, 360583873153623582, 360583873698315702, 360583873698642992, 360583872660042280, 360583871214576018, 360583869912180826, 360583870753578802, 360583870791908599, 360583870830288077]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 25050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 25000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598017536610747, 360598021258438652⟩, ⟨(-354598604890660388), (-354535484235474066)⟩, true⟩

def words06 : List Nat := [360583871554169383, 360583873071978183, 360583875661275136, 360583878250429388, 360583879444940481, 360583879574103203, 360583879657427588, 360583879740836330, 360583879741103288, 360583880000242511]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 25060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 25000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360572749319201069, 360572753044149582⟩, ⟨279089461694422580, 279152660598423622⟩, true⟩

def words07 : List Nat := [360583880000534488, 360583879582137942, 360583880331562863, 360583882678575237, 360583883899566005, 360583885120511577, 360583885338554401, 360583885338882030, 360583883976449822, 360583883533009169]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 25070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 25000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360560196457670260, 360560200185706074⟩, ⟨593675314890568203, 593738591239877743⟩, true⟩

def words08 : List Nat := [360583883089497203, 360583882600987030, 360583880532303939, 360583877645453181, 360583874758779613, 360583871107011564, 360583868476067340, 360583867430221547, 360583866384417838, 360583864537688533]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 25080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 25000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587343667076353, 360587347398206008⟩, ⟨(-87785135382047430), (-87721781393052418)⟩, true⟩

def words09 : List Nat := [360583863594814544, 360583862882476525, 360583862182551298, 360583862182879149, 360583860616341622, 360583857520719405, 360583854425281398, 360583852913469358, 360583852506177297, 360583852645750208]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 25090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 25000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 25000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk250B
