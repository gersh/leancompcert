import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk309

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360559403276724788, 360559409034102365⟩, ⟨731313363821444821, 731433672222070047⟩, true⟩

def state01 : KState := ⟨⟨360546348591474705, 360546354352717870⟩, ⟨1134574138352363688, 1134694566219468128⟩, true⟩

def words00 : List Nat := [360583079261037927, 360583078801056720, 360583077296836881, 360583075272172892, 360583073247578968, 360583070498326592, 360583068537441238, 360583067191464939, 360583065845531020, 360583063979577122]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 30900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 30900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607792909356811, 360607798674481312⟩, ⟨(-764894220516397521), (-764773672658120915)⟩, true⟩

def words01 : List Nat := [360583062792318426, 360583062647660407, 360583062819201496, 360583063412645561, 360583063413028143, 360583063083835658, 360583063076074430, 360583063925742368, 360583064726040086, 360583065526372968]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 30910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 30900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584928691376476, 360584934460412551⟩, ⟨(-58198399305896501), (-58077730482144751)⟩, true⟩

def words02 : List Nat := [360583065526741496, 360583065519455696, 360583064468963956, 360583063649463745, 360583062829904242, 360583061737368107, 360583060825584707, 360583059198339114, 360583057571120294, 360583056805940270]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 30920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 30900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360539879666583667, 360539885439496998⟩, ⟨1335496031942227295, 1335616820708438429⟩, true⟩

def words03 : List Nat := [360583057907940305, 360583059009951407, 360583059319676165, 360583059320087160, 360583058587221311, 360583057269451074, 360583055951645920, 360583055674687282, 360583054798791964, 360583053403967213]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 30930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 30900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360559040756787396, 360559046533576976⟩, ⟨742577210605799303, 742698119322710223⟩, true⟩

def words04 : List Nat := [360583052009129469, 360583051850276251, 360583051850611345, 360583051719438371, 360583051588241805, 360583050560658764, 360583048491333985, 360583046394733459, 360583044298148296, 360583043241794188]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 30940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 30900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360551058021571010, 360551063802281958⟩, ⟨989650745601320323, 989771775703257879⟩, true⟩

def words05 : List Nat := [360583042466851918, 360583041066086914, 360583039665335323, 360583038570734366, 360583038518637040, 360583037930088172, 360583037341533432, 360583036009355472, 360583034207044817, 360583033174882193]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 30950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 30900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360529662453028124, 360529668237618482⟩, ⟨1651994516035826728, 1652115666263637678⟩, true⟩

def words06 : List Nat := [360583032142651622, 360583031083497714, 360583029284401055, 360583026967199459, 360583024650082805, 360583021630914801, 360583019279614784, 360583017728869339, 360583016178176170, 360583013916219181]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 30960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 30900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599291034394008, 360599296822868390⟩, ⟨(-504739809400919783), (-504618538865393251)⟩, true⟩

def words07 : List Nat := [360583012194112465, 360583011510678928, 360583010842923287, 360583010843335980, 360583010531487052, 360583009191807341, 360583007852132772, 360583007770206149, 360583008296333199, 360583008822517679]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 30970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 30900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360562108839119889, 360562114631516290⟩, ⟨647327991008194101, 647449383067811545⟩, true⟩

def words08 : List Nat := [360583008822884961, 360583008677281323, 360583009497709461, 360583010426999720, 360583011091433303, 360583011091845037, 360583010717467698, 360583009553328636, 360583008389192424, 360583006834906668]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 30980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 30900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360519882021505222, 360519887817780987⟩, ⟨1956155930248652190, 1956277442548875722⟩, true⟩

def words09 : List Nat := [360583006161102915, 360583005833300164, 360583005505471756, 360583004660597264, 360583002777232069, 360583000629976834, 360582998482727213, 360582997095887597, 360582995577041326, 360582993541734177]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 30990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 30900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 30900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk309
