import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk191

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362505095236997589, 362505100101675717⟩, ⟨(-365555153864193220), (-365492309408737398)⟩, true⟩

def state01 : KState := ⟨⟨362440737007221713, 362440741877235672⟩, ⟨863788360446149492, 863851306843023542⟩, true⟩

def words00 : List Nat := [371285966398737848, 371285966399328512, 371285963774800980, 371285962301649439, 371285960828353448, 371285960198031587, 371285956427558912, 371285952196962468, 371285947966573299, 371285946027253622]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 19100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 19100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362417631350382725, 362417636225717435⟩, ⟨1305631407739489500, 1305694455843341510⟩, true⟩

def words01 : List Nat := [371285943662308165, 371285943355890683, 371285943049302140, 371285942508804560, 371285939171918489, 371285936678856029, 371285934185756097, 371285932845301591, 371285929255845522, 371285925684705058]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 19110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 19100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362428265322726442, 362428270203348060⟩, ⟨1102537607864586213, 1102600757081737381⟩, true⟩

def words02 : List Nat := [371285922113668969, 371285921263388601, 371285919039693748, 371285918602420438, 371285918165009813, 371285917015514732, 371285912746021487, 371285910738442770, 371285908730767362, 371285907461951392]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 19120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 19100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362443010252081513, 362443015138094338⟩, ⟨820312073838409166, 820375326215915674⟩, true⟩

def words03 : List Nat := [371285904449633648, 371285900864981090, 371285897280470095, 371285895443284448, 371285892256970034, 371285889551089293, 371285886845280343, 371285884157129768, 371285879201642392, 371285876962870510]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 19130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 19100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362423597962479767, 362423602853753381⟩, ⟨1192119795844152234, 1192183148941262302⟩, true⟩

def words04 : List Nat := [371285875200558160, 371285875201151542, 371285872897604914, 371285870594149681, 371285868290711397, 371285866052984764, 371285862445712544, 371285860920706431, 371285859395667865, 371285857848476163]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 19140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 19100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362460119933356100, 362460124829995189⟩, ⟨492627067584279969, 492690523456138859⟩, true⟩

def words05 : List Nat := [371285854598137167, 371285852758164596, 371285851447977924, 371285851448570175, 371285848814032161, 371285845717521855, 371285842621100359, 371285842236861311, 371285840708205100, 371285839366710019]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 19150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 19100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487236605541307, 362487241507528722⟩, ⟨(-27105681816829160), (-27042123443472404)⟩, true⟩

def words06 : List Nat := [371285838025132315, 371285836661812830, 371285833786416327, 371285833621519022, 371285834126554383, 371285834127157480, 371285832785235573, 371285831459018488, 371285830858780003, 371285830933044164]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 19160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 19100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362428932027669806, 362428936934993504⟩, ⟨1091027748861964468, 1091091409559252224⟩, true⟩

def words07 : List Nat := [371285832977540325, 371285835022057132, 371285836253484410, 371285836254077216, 371285833871074529, 371285831743650554, 371285829778970573, 371285829779563682, 371285826835232843, 371285823869798471]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 19170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 19100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482861155701347, 362482866068332717⟩, ⟨56610593238791001, 56674355763954601⟩, true⟩

def words08 : List Nat := [371285820904405145, 371285820643227546, 371285820587420928, 371285821911525311, 371285822775672023, 371285822776265421, 371285820508405185, 371285819384715882, 371285819395271629, 371285819395886858]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 19180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 19100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488294992756322, 362488299910797206⟩, ⟨(-47655817452035345), (-47591951091246815)⟩, true⟩

def words09 : List Nat := [371285819242439374, 371285819105807937, 371285820571998364, 371285821216291351, 371285821895335223, 371285822574526768, 371285823262190003, 371285823262784277, 371285821162601083, 371285821292439244]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 19190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 19100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 19100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk191
