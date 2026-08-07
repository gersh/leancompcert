import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk430

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482367168046565, 362482393559790039⟩, ⟨128888551876992592, 129655342035096242⟩, true⟩

def state01 : KState := ⟨⟨362497390303015131, 362497416707482835⟩, ⟨(-517179872431088701), (-516412535068361993)⟩, true⟩

def words00 : List Nat := [371285408884144057, 371285408885720512, 371285409196246290, 371285409623449727, 371285409936447947, 371285409937866110, 371285409529725932, 371285409519239779, 371285409904439515, 371285410185080000]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 43000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 43000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362505346811703020, 362505373229067680⟩, ⟨(-859408911910028204), (-858641019783308788)⟩, true⟩

def words01 : List Nat := [371285410425836381, 371285410667035763, 371285411449177022, 371285411997198108, 371285412571946572, 371285413147209200, 371285413725941871, 371285413727360763, 371285414114810685, 371285414580505738]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 43010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 43000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494374380528276, 362494400810545750⟩, ⟨(-387278771011180776), (-386510334494259832)⟩, true⟩

def words02 : List Nat := [371285415321499849, 371285415622402484, 371285415920845411, 371285416219771133, 371285416685752868, 371285416900590960, 371285417453197939, 371285418006341263, 371285418463392604, 371285418673609722]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 43020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 43000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362526760399055942, 362526786841919792⟩, ⟨(-1781031275015807703), (-1780262285655234141)⟩, true⟩

def words03 : List Nat := [371285419301439738, 371285419929997841, 371285420940759916, 371285421231929433, 371285421447096728, 371285421662708335, 371285422418550277, 371285422906962988, 371285423868984462, 371285424831612057]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 43030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 43000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489139671836073, 362489166127514728⟩, ⟨(-161780479020507297), (-161010938045314051)⟩, true⟩

def words04 : List Nat := [371285425791889785, 371285426032770680, 371285426252757848, 371285426473429769, 371285426854035469, 371285426855455288, 371285426516566941, 371285426176392719, 371285426034389397, 371285426122914480]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 43040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 43000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362482959708636125, 362482986177087919⟩, ⟨104445925680408975, 105216016602413701⟩, true⟩

def words05 : List Nat := [371285426751164308, 371285427379949357, 371285428007982083, 371285428280894806, 371285428705203532, 371285429130238433, 371285429777410754, 371285429778830921, 371285429706861159, 371285429651695500]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 43050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 43000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362498698113781251, 362498724594936184⟩, ⟨(-573282341571554364), (-572511703587295658)⟩, true⟩

def words06 : List Nat := [371285429840491497, 371285429842055952, 371285430335877583, 371285430853940543, 371285431200416318, 371285431201836974, 371285431158357741, 371285431407863544, 371285432006894909, 371285432316986118]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 43060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 43000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362508959596482155, 362508986090612535⟩, ⟨(-1015311959569897206), (-1014540762667927096)⟩, true⟩

def words07 : List Nat := [371285432534246565, 371285432751977419, 371285433359841672, 371285433700177900, 371285434207309062, 371285434714956329, 371285435218882087, 371285435384222255, 371285435931861787, 371285436480281579]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 43070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 43000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362496463644710767, 362496490151483378⟩, ⟨(-476862144109199065), (-476090402512971197)⟩, true⟩

def words08 : List Nat := [371285437481733250, 371285437972666375, 371285438461594510, 371285438950956417, 371285439466893779, 371285439747326999, 371285440303223230, 371285440859682852, 371285441405464429, 371285441663341702]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 43080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 43000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362528121949947216, 362528148469579168⟩, ⟨(-1841129374338086621), (-1840357078569776589)⟩, true⟩

def words09 : List Nat := [371285442328995087, 371285442995387185, 371285444200322801, 371285444827438766, 371285445381898290, 371285445936778331, 371285446951078179, 371285447776077977, 371285448767795388, 371285449760069650]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 43090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 43000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 43000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk430
