import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk913

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579440646746946, 360579495499684880⟩, ⟨223954444203702155, 227336261568840543⟩, true⟩

def state01 : KState := ⟨⟨360594585303846116, 360594640169240385⟩, ⟨(-1158856081213382395), (-1155473126522286463)⟩, true⟩

def words00 : List Nat := [360581985465409585, 360581985467234274, 360581985618351048, 360581985769717635, 360581985818314455, 360581985819634000, 360581985783304313, 360581985739361853, 360581985769378085, 360581985909331697]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 91300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 91300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584800844322035, 360584855722276184⟩, ⟨(-265382836403398737), (-261998734808535899)⟩, true⟩

def words01 : List Nat := [360581985958875962, 360581986008561533, 360581986153521810, 360581986375583612, 360581986514340546, 360581986653291276, 360581986721514785, 360581986722834404, 360581986702649679, 360581986735572047]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 91310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 91300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589277524613490, 360589332415013535⟩, ⟨(-674210289484840771), (-670825051269654487)⟩, true⟩

def words02 : List Nat := [360581986781888504, 360581986893587238, 360581986938270380, 360581986983089112, 360581986984200049, 360581987008051309, 360581987151216534, 360581987294631676, 360581987345747620, 360581987427536450]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 91320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 91300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599231749251019, 360599286652106908⟩, ⟨(-1583432781199719031), (-1580046405330931515)⟩, true⟩

def words03 : List Nat := [360581987628761442, 360581987830384313, 360581987972932270, 360581987996036657, 360581987997253888, 360581987918366772, 360581987853298741, 360581987944790330, 360581988135245257, 360581988325995623]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 91330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 91300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583238456892851, 360583293372347792⟩, ⟨(-122648359994356409), (-119260833269651585)⟩, true⟩

def words04 : List Nat := [360581988435565048, 360581988451747406, 360581988465074748, 360581988478780899, 360581988479885450, 360581988463482553, 360581988327281323, 360581988131125896, 360581987934721170, 360581987849329220]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 91340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 91300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360548879327784401, 360548934255664349⟩, ⟨3016255155042919523, 3019643816855462097⟩, true⟩

def words05 : List Nat := [360581987900935178, 360581987952790872, 360581987953967498, 360581987927492610, 360581987781171555, 360581987551359169, 360581987321181385, 360581987060312719, 360581986759435138, 360581986399018722]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 91350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 91300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585587882014336, 360585642822351711⟩, ⟨(-337632285459218037), (-334242485473249271)⟩, true⟩

def words06 : List Nat := [360581986038310662, 360581985770797086, 360581985562972237, 360581985454973220, 360581985346844542, 360581985136906939, 360581984908289028, 360581984799710935, 360581984700316477, 360581984741719200]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 91360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 91300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360580117473673840, 360580172426605421⟩, ⟨162228613283563014, 165619564062091720⟩, true⟩

def words07 : List Nat := [360581984742918531, 360581984684693843, 360581984686293369, 360581984824869508, 360581984880122006, 360581984935584016, 360581984936785300, 360581984889461775, 360581984871766768, 360581984853439106]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 91370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 91300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585005202526459, 360585060167889076⟩, ⟨(-284483338873740041), (-281091252085905677)⟩, true⟩

def words08 : List Nat := [360581984934442652, 360581984935763155, 360581984917146320, 360581984832728097, 360581984748115826, 360581984580562582, 360581984483516561, 360581984495587626, 360581984496764604, 360581984468399128]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 91380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 91300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360594013476395885, 360594068454235949⟩, ⟨(-1107770726968995175), (-1104377499804140197)⟩, true⟩

def words09 : List Nat := [360581984584207656, 360581984700430861, 360581984935812549, 360581985051911103, 360581985067792588, 360581985083764048, 360581985219052319, 360581985414762151, 360581985548055200, 360581985681620725]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 91390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 91300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 91300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk913
