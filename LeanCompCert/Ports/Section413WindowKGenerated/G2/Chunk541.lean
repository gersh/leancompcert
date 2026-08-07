import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk541

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360562829752027083, 360562848231254341⟩, ⟨1028136889086125181, 1028812361822995175⟩, true⟩

def state01 : KState := ⟨⟨360594790302771781, 360594808789097488⟩, ⟨(-701087355251085591), (-700411498452804521)⟩, true⟩

def words00 : List Nat := [360581864744714009, 360581864932727584, 360581865034562245, 360581865136526331, 360581865137219031, 360581864948263742, 360581864662126679, 360581864615781695, 360581864572847989, 360581864812855083]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360562875063534644, 360562893557014738⟩, ⟨1026086159384653506, 1026762403341656858⟩, true⟩

def words01 : List Nat := [360581864815602116, 360581864818430977, 360581865055870246, 360581865507347822, 360581865813930105, 360581866120623674, 360581866163071814, 360581866163823317, 360581865865383981, 360581865515686979]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570828235889624, 360570846736438169⟩, ⟨595591520752952561, 596268147290400693⟩, true⟩

def words02 : List Nat := [360581865165747557, 360581865156717050, 360581864806820048, 360581864286208393, 360581863765481164, 360581863149018416, 360581862751366977, 360581862631308669, 360581862511170754, 360581862220408064]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360584045602689832, 360584064110342958⟩, ⟨(-120114687206630355), (-119437676063675881)⟩, true⟩

def words03 : List Nat := [360581862017535421, 360581861527943034, 360581861038144503, 360581860889080883, 360581860399333303, 360581859620490797, 360581858841533254, 360581858278643330, 360581858020239677, 360581858061764918]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574380310174445, 360574398824986782⟩, ⟨403111987896078323, 403789386673002655⟩, true⟩

def words04 : List Nat := [360581858062434659, 360581857933311468, 360581858048993890, 360581858198663251, 360581858199308343, 360581858018022661, 360581857496110961, 360581856803758600, 360581856111287899, 360581855692700042]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360546916454867083, 360546934976766481⟩, ⟨1890493814791575677, 1891171597369360047⟩, true⟩

def words05 : List Nat := [360581855758218778, 360581855961592098, 360581855962272704, 360581855899449973, 360581855496031723, 360581855006853782, 360581854517473965, 360581854235043894, 360581853855534811, 360581853211577585]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 54150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 54100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360609677884952551, 360609696413950259⟩, ⟨(-1508955015939742403), (-1508276848883661719)⟩, true⟩

def words06 : List Nat := [360581852567474120, 360581852126275020, 360581852106372155, 360581852266946692, 360581852267641174, 360581852102133894, 360581852312871748, 360581852588809788, 360581853015555258, 360581853530324636]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 54160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 54100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360574506409602466, 360574524945780623⟩, ⟨396446833885222294, 397125389940270156⟩, true⟩

def words07 : List Nat := [360581853832214940, 360581854134167443, 360581854353086067, 360581854743595470, 360581854908792951, 360581855074102065, 360581855074772246, 360581855069817048, 360581854821603474, 360581854687197018]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 54170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 54100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360568827980262378, 360568846523522083⟩, ⟨704136362881466007, 704815302650655323⟩, true⟩

def words08 : List Nat := [360581854757165460, 360581854757917802, 360581854623141217, 360581854318271887, 360581854013287589, 360581853622805002, 360581853494549580, 360581853358570251, 360581853222517511, 360581852895595356]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 54180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 54100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603672102259964, 360603690652620482⟩, ⟨(-1184224127890208753), (-1183544803292564741)⟩, true⟩

def words09 : List Nat := [360581852656194106, 360581852647851312, 360581852969856167, 360581853345767602, 360581853431341577, 360581853516973121, 360581853517588588, 360581853628348021, 360581854031853688, 360581854435515769]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 54190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 54100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 54100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk541
