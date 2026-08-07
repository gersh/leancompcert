import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk250

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360536683811519857, 360536687511688331⟩, ⟨1179395031823839449, 1179457610235706293⟩, true⟩

def state01 : KState := ⟨⟨360571232642946366, 360571236346197110⟩, ⟨315432710670963022, 315495366154870304⟩, true⟩

def words00 : List Nat := [360583863929305755, 360583862769941857, 360583862410093720, 360583862282116266, 360583862154117285, 360583860677299146, 360583857611657150, 360583855059557622, 360583852507566988, 360583851114935810]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360608753510529154, 360608757216898438⟩, ⟨(-623243465492454417), (-623180731998655461)⟩, true⟩

def words01 : List Nat := [360583850610865841, 360583848853480095, 360583847096170939, 360583848013668466, 360583848685739740, 360583849357810591, 360583849358102077, 360583849115413963, 360583849913085553, 360583850908917197]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570100707919132, 360570104417366615⟩, ⟨343958166243345319, 344020976769052329⟩, true⟩

def words02 : List Nat := [360583853062744895, 360583853629201942, 360583853629493914, 360583853216452496, 360583852803397763, 360583850804232431, 360583849885615946, 360583849803869586, 360583849722097170, 360583848763222351]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360635799193439792, 360635802905977948⟩, ⟨(-1300736380308034760), (-1300673492407363954)⟩, true⟩

def words03 : List Nat := [360583849257014468, 360583850299917754, 360583852934178942, 360583853982324884, 360583853982626428, 360583853687046992, 360583854686806565, 360583857001284306, 360583859076070579, 360583861150760211]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360634815305218299, 360634819020870332⟩, ⟨(-1276396706482705889), (-1276333740595215781)⟩, true⟩

def words04 : List Nat := [360583862126774368, 360583862431078931, 360583863871753672, 360583865312408782, 360583866344923344, 360583867420615939, 360583867420912527, 360583867169129231, 360583867573766863, 360583869608048680]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk250
