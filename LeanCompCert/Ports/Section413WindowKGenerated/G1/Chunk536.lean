import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk536

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487513109565499, 362487554855725056⟩, ⟨(-137975372455007764), (-136463753223207272)⟩, true⟩

def state01 : KState := ⟨⟨362471709005205597, 362471750767575501⟩, ⟨709105234094478692, 710617722286423162⟩, true⟩

def words00 : List Nat := [371285008945817428, 371285008947616423, 371285008492011302, 371285008217488551, 371285007942087880, 371285007741551908, 371285007254151388, 371285006749743435, 371285006244607605, 371285006087894219]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 53600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 53600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478712020541922, 362478753799128920⟩, ⟨333691722420871802, 335205080094041914⟩, true⟩

def words01 : List Nat := [371285005942178959, 371285006044433807, 371285006051569126, 371285006053380617, 371285005750013833, 371285005554223585, 371285005507019867, 371285005508828295, 371285005407155607, 371285005292603259]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 53610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 53600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484685952140058, 362484727746817065⟩, ⟨13381094827145976, 14895315328814464⟩, true⟩

def words02 : List Nat := [371285005273530096, 371285005275533482, 371285005466922692, 371285005737678364, 371285005929958806, 371285005931758514, 371285005660607465, 371285005488018439, 371285005487173911, 371285005489038375]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 53620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 53600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495765344320444, 362495807155441582⟩, ⟨(-580861185558021920), (-579346083076008128)⟩, true⟩

def words03 : List Nat := [371285005485218514, 371285005438491665, 371285005689623372, 371285005864019017, 371285006067492033, 371285006271642663, 371285006459302874, 371285006461111819, 371285006517771237, 371285006721387855]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 53630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 53600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473624953714168, 362473666780881708⟩, ⟨606836632099880487, 608352595395103255⟩, true⟩

def words04 : List Nat := [371285007019120984, 371285007020921493, 371285006855712795, 371285006690886106, 371285006525393267, 371285006467143327, 371285006234873212, 371285006179639700, 371285006123757319, 371285006065045643]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 53640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 53600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362503504934204432, 362503546777622975⟩, ⟨(-996382119376339815), (-994865284132231799)⟩, true⟩

def words05 : List Nat := [371285005874345292, 371285005895909389, 371285006263623438, 371285006265424359, 371285006207282561, 371285006077505940, 371285006162280289, 371285006263312082, 371285006610054189, 371285006957564977]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 53650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 53600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474804073803514, 362474845933490025⟩, ⟨543901998296560819, 545419706561908473⟩, true⟩

def words06 : List Nat := [371285007302488257, 371285007359653163, 371285007720697303, 371285008082697540, 371285008550219466, 371285008555670235, 371285008557029917, 371285008529566837, 371285008501422976, 371285008402403048]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 53660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 53600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362461474497012739, 362461516372945491⟩, ⟨1259469018341138278, 1260987598622705318⟩, true⟩

def words07 : List Nat := [371285008346142457, 371285008479972239, 371285008613011521, 371285008614813580, 371285008350011822, 371285008172173277, 371285008044089600, 371285008045891156, 371285007635598758, 371285007200043530]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 53670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 53600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482724335615597, 362482766227680639⟩, ⟨118691340677036998, 120210787023544246⟩, true⟩

def words08 : List Nat := [371285006763665718, 371285006674743072, 371285006438687162, 371285006347131526, 371285006255048543, 371285006109036683, 371285005609300916, 371285005377498044, 371285005204857753, 371285005206764706]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 53680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 53600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486919370149184, 362486961278600906⟩, ⟨(-106537807625148485), (-105017481394634319)⟩, true⟩

def words09 : List Nat := [371285005166420304, 371285005064327875, 371285005204008201, 371285005318876664, 371285005539490488, 371285005760811102, 371285005914171614, 371285005915974012, 371285005643586463, 371285005682217326]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 53690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 53600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 53600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk536
