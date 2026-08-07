import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk895

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569243705856612, 360569296335820064⟩, ⟨1138303593645360900, 1141484447024440782⟩, true⟩

def state01 : KState := ⟨⟨360565567656862886, 360565620299029940⟩, ⟨1467412555387299220, 1470594501047690784⟩, true⟩

def words00 : List Nat := [360582050210529919, 360582050272886880, 360582050354332666, 360582050436023014, 360582050437235037, 360582050404778387, 360582050247400982, 360582050074317251, 360582049900878536, 360582049686819547]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 89500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 89500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582307819306074, 360582360473763881⟩, ⟨(-31121506504622225), (-27938460637495509)⟩, true⟩

def words01 : List Nat := [360582049504423735, 360582049259542275, 360582049014418515, 360582048894344664, 360582048836711504, 360582048747802637, 360582048658730788, 360582048497084477, 360582048380460592, 360582048385419945]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 89510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 89500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594893080530142, 360594945747162505⟩, ⟨(-1157837544322943561), (-1154653408528773053)⟩, true⟩

def words02 : List Nat := [360582048514584386, 360582048602999516, 360582048604182261, 360582048587350184, 360582048570308957, 360582048548849380, 360582048701582080, 360582048854562799, 360582048913360490, 360582049058769337]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 89520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 89500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591098235015811, 360591150913833733⟩, ⟨(-818065538915493010), (-814880312088127016)⟩, true⟩

def words03 : List Nat := [360582049197596384, 360582049336809366, 360582049600236339, 360582049770768948, 360582049831168886, 360582049891667568, 360582049948955441, 360582050069212433, 360582050171900648, 360582050274885228]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 89530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 89500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580388068538185, 360580440759659424⟩, ⟨140880978715017659, 144067307241435991⟩, true⟩

def words04 : List Nat := [360582050315802577, 360582050317094146, 360582050246750019, 360582050261642211, 360582050262722932, 360582050245959603, 360582050104483928, 360582049887690727, 360582049670654502, 360582049551476749]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 89540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 89500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360550779889359427, 360550832592658469⟩, ⟨2792415851471372341, 2795603270581868473⟩, true⟩

def words05 : List Nat := [360582049534581105, 360582049453447081, 360582049372172785, 360582049228447793, 360582048959957551, 360582048660350379, 360582048360371555, 360582048081029243, 360582047804427416, 360582047457225038]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 89550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 89500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592917827213518, 360592970542705619⟩, ⟨(-981653863464538447), (-978465352284475257)⟩, true⟩

def words06 : List Nat := [360582047109737245, 360582046887175339, 360582046789309692, 360582046803409486, 360582046804621638, 360582046699067461, 360582046539058684, 360582046503960411, 360582046511526787, 360582046634830476]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 89560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 89500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564676542171506, 360564729269974197⟩, ⟨1548092261554751000, 1551281875456157262⟩, true⟩

def words07 : List Nat := [360582046689787838, 360582046744907744, 360582046761381735, 360582046840757626, 360582046888026334, 360582046935503683, 360582046936666244, 360582046901222245, 360582046741071214, 360582046549226890]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 89570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 89500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566169127555051, 360566221867534292⟩, ⟨1414324459015083002, 1417515163750273546⟩, true⟩

def words08 : List Nat := [360582046356958013, 360582046232824270, 360582046025513481, 360582045739595138, 360582045453467894, 360582045065035150, 360582044772471642, 360582044574236087, 360582044375863996, 360582044115148427]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 89580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 89500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583629752239388, 360583682504429377⟩, ⟨(-150113643735580007), (-146921844977708617)⟩, true⟩

def words09 : List Nat := [360582043939587698, 360582043888857074, 360582043837766100, 360582043783926469, 360582043605572802, 360582043307979641, 360582043010139195, 360582042837115435, 360582042750332428, 360582042769995859]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 89590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 89500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 89500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk895
