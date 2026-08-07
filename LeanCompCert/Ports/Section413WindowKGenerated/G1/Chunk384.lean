import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk384

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497778049808421, 362497798904698406⟩, ⟨(-488734332567126690), (-488193152069692546)⟩, true⟩

def state01 : KState := ⟨⟨362495959631780516, 362495980497859752⟩, ⟨(-418852506037275194), (-418310895814140250)⟩, true⟩

def words00 : List Nat := [371285086547408040, 371285086836904947, 371285087029975013, 371285087223435964, 371285087621819609, 371285087718888863, 371285088461666300, 371285089204926141, 371285089819760122, 371285090104591831]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 38400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 38400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362536839804991644, 362536860682417503⟩, ⟨(-1989263601367810183), (-1988721555264576197)⟩, true⟩

def words01 : List Nat := [371285090966736371, 371285091829495403, 371285093287774300, 371285093843919366, 371285094363322006, 371285094883124228, 371285095907142679, 371285096668728763, 371285098016900871, 371285099365552649]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 38410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 38400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492213959879302, 362492234848658735⟩, ⟨(-274647565948313925), (-274105083582779069)⟩, true⟩

def words02 : List Nat := [371285100700217082, 371285101133093665, 371285101648632650, 371285102164784702, 371285102784318692, 371285102785575102, 371285102503274525, 371285102220283107, 371285102266298691, 371285102453363719]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 38420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 38400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362467609855273214, 362467630755364086⟩, ⟨671186262924902288, 671729180048301440⟩, true⟩

def words03 : List Nat := [371285103316573519, 371285104180266293, 371285104975471420, 371285105167571438, 371285105565118606, 371285105963251305, 371285106408151916, 371285106409408645, 371285105953088565, 371285105499902284]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 38430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 38400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491454788905207, 362491475700248296⟩, ⟨(-245502742494688781), (-244959392779166217)⟩, true⟩

def words04 : List Nat := [371285105046173165, 371285105043901159, 371285104955819422, 371285105176153621, 371285105180861595, 371285105182119095, 371285104421319948, 371285104337399736, 371285104843476793, 371285105010467038]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 38440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 38400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362522387673085238, 362522408595884307⟩, ⟨(-1435053430559393151), (-1434509640303804037)⟩, true⟩

def words05 : List Nat := [371285105046136396, 371285105082200350, 371285105793802725, 371285106336869527, 371285107085365157, 371285107834327868, 371285108585762502, 371285108881059561, 371285109851744497, 371285110823067589]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 38450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 38400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491650116490016, 362491671050480220⟩, ⟨(-252651973048550353), (-252107752322679583)⟩, true⟩

def words06 : List Nat := [371285112469446143, 371285113215938630, 371285113960811966, 371285114706088649, 371285115462451067, 371285115880453859, 371285116483639505, 371285117087283930, 371285117689357018, 371285117861004442]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 38460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 38400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362510812658820049, 362510833604217386⟩, ⟨(-989915204570527965), (-989370544956696711)⟩, true⟩

def words07 : List Nat := [371285118353517275, 371285118846689102, 371285119942917547, 371285120139867185, 371285120267100760, 371285120394694596, 371285121126174123, 371285121640971832, 371285122310032032, 371285122979624556]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 38470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 38400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488235079095856, 362488256035832062⟩, ⟨(-121076856373220354), (-120531760380299108)⟩, true⟩

def words08 : List Nat := [371285123598345656, 371285123599604144, 371285123741903304, 371285124064833532, 371285124536872707, 371285124538152874, 371285124450757814, 371285124362663328, 371285124525943858, 371285124608735331]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 38480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 38400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473578845621287, 362473599813698220⟩, ⟨443232946237777788, 443778478791975370⟩, true⟩

def words09 : List Nat := [371285125258304433, 371285125908339568, 371285126451271313, 371285126452532732, 371285126355828936, 371285126411344356, 371285127066920795, 371285127068179630, 371285126825398952, 371285126527433077]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 38490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 38400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 38400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk384
