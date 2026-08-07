import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk853

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360551895787100627, 360551943416058468⟩, ⟨2595635210518859242, 2598378885592302198⟩, true⟩

def state01 : KState := ⟨⟨360583943550761361, 360583991191311827⟩, ⟨(-138150416121873591), (-135405752141996875)⟩, true⟩

def words00 : List Nat := [360582404711589827, 360582404471620831, 360582404336566507, 360582404338428666, 360582404339567290, 360582404205394026, 360582404099118484, 360582404057856639, 360582404016253365, 360582403989753506]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 85300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 85300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584264900752387, 360584312552985128⟩, ⟨(-165543738406603407), (-162798077754627485)⟩, true⟩

def words01 : List Nat := [360582403990855897, 360582403942224898, 360582403980785229, 360582404154205870, 360582404278107496, 360582404402236090, 360582404457262599, 360582404458489739, 360582404463459481, 360582404487236314]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 85310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 85300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581529384662950, 360581577048456368⟩, ⟨67816741944998855, 70563389011627853⟩, true⟩

def words02 : List Nat := [360582404591811426, 360582404618217423, 360582404619331837, 360582404519158930, 360582404418789374, 360582404282968099, 360582404215918258, 360582404170491337, 360582404124944294, 360582403995473966]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 85320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 85300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360597882687122241, 360597930362486277⟩, ⟨(-1327689328396679586), (-1324941693951349960)⟩, true⟩

def words03 : List Nat := [360582404114300364, 360582404243181436, 360582404508906751, 360582404637575511, 360582404649367591, 360582404661254872, 360582404662263632, 360582404730744539, 360582404913662811, 360582405096858369]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 85330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 85300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579546405618420, 360579594092659697⟩, ⟨237150919571694893, 239899550610365867⟩, true⟩

def words04 : List Nat := [360582405210991073, 360582405230460143, 360582405333600139, 360582405437120764, 360582405453073983, 360582405454300511, 360582405364326257, 360582405191274571, 360582405017995967, 360582404866539139]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 85340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 85300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360555381850188360, 360555429548798356⟩, ⟨2299682433524644415, 2302432052010570219⟩, true⟩

def words05 : List Nat := [360582404834616054, 360582404772492950, 360582404710238612, 360582404561026894, 360582404274404099, 360582403929753608, 360582403584741032, 360582403286577297, 360582403060002460, 360582402745283954]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 85350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 85300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583499413658672, 360583547123827008⟩, ⟨(-100541808350744160), (-97791203185927388)⟩, true⟩

def words06 : List Nat := [360582402430285856, 360582402252783188, 360582402211438697, 360582402260059320, 360582402261221160, 360582402180206841, 360582401961774056, 360582401804081797, 360582401646032956, 360582401638788929]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 85360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 85300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360568556650167275, 360568604372039079⟩, ⟨1175231983705010123, 1177983588051251935⟩, true⟩

def words07 : List Nat := [360582401639894577, 360582401544420309, 360582401448691971, 360582401538538237, 360582401598005405, 360582401657673005, 360582401658766111, 360582401639167363, 360582401482201370, 360582401322004543]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 85370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 85300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584339338365069, 360584387071788782⟩, ⟨(-172364868027439906), (-169612277320570934)⟩, true⟩

def words08 : List Nat := [360582401161403636, 360582401138113920, 360582401093985827, 360582400970659864, 360582400847130739, 360582400689396485, 360582400698633945, 360582400756630756, 360582400757723944, 360582400770219290]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 85380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 85300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360572167959506236, 360572215704530785⟩, ⟨866969489332376287, 869723070691688889⟩, true⟩

def words09 : List Nat := [360582400841074486, 360582400912298456, 360582400913314597, 360582400914464872, 360582400778429974, 360582400525950158, 360582400273245163, 360582400061686105, 360582399933387690, 360582399815428815]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 85390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 85300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 85300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk853
