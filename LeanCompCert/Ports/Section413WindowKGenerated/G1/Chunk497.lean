import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk497

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491549263683635, 362491584938135120⟩, ⟨(-328504034323410950), (-327306180352420594)⟩, true⟩

def state01 : KState := ⟨⟨362464903993212339, 362464939682602957⟩, ⟨995860398017695028, 997058994540783546⟩, true⟩

def words00 : List Nat := [371284999567847896, 371284999569505860, 371284999165066968, 371284999050886578, 371284998945234057, 371284998946893570, 371284998518853413, 371284998008531799, 371284997497574347, 371284997196071893]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 49700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 49700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362465450533026803, 362465486237364890⟩, ⟨968798031106254326, 969997370743615074⟩, true⟩

def words01 : List Nat := [371284996794026029, 371284996796166271, 371284996797406596, 371284996783876970, 371284996494353266, 371284996283615297, 371284996217263965, 371284996218922489, 371284995826792658, 371284995436293764]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 49710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 49700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482398966388937, 362482434685595795⟩, ⟨126039022446691311, 127239101432923631⟩, true⟩

def words02 : List Nat := [371284995045065678, 371284994823966088, 371284994399679177, 371284994271000003, 371284994141847338, 371284993958738969, 371284993394777120, 371284993235245517, 371284993282339141, 371284993284056140]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 49720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 49700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482120417475909, 362482156151759814⟩, ⟨139876560986591158, 141077389832576388⟩, true⟩

def words03 : List Nat := [371284993233856396, 371284993101438713, 371284993140094386, 371284993141940842, 371284993117402383, 371284993076201712, 371284993034429286, 371284992962528690, 371284992503286758, 371284992448298467]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 49730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 49700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494463757727274, 362494499506809229⟩, ⟨(-474034067646314241), (-472832502668206057)⟩, true⟩

def words04 : List Nat := [371284992738693874, 371284992947520868, 371284993154539096, 371284993362118422, 371284993694339452, 371284993824965838, 371284994358116181, 371284994891904198, 371284995334181426, 371284995526936097]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 49740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 49700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362508708837463027, 362508744601564820⟩, ⟨(-1182827506780759313), (-1181625194489025661)⟩, true⟩

def words05 : List Nat := [371284995913119942, 371284996300174125, 371284996894802956, 371284996952115129, 371284996971453974, 371284996991322842, 371284997413555131, 371284997634289588, 371284998112649311, 371284998591748116]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 49750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 49700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483086239654959, 362483122018768410⟩, ⟨92186915068243256, 93389974413689682⟩, true⟩

def words06 : List Nat := [371284999026152682, 371284999027812728, 371284999080122951, 371284999192303108, 371284999367659569, 371284999369319936, 371284999053251590, 371284998730998504, 371284998447895306, 371284998449839612]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 49760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 49700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362454955441455047, 362454991235497738⟩, ⟨1492512709506402970, 1493716511955990414⟩, true⟩

def words07 : List Nat := [371284998727468966, 371284999043448889, 371284999335165091, 371284999336826340, 371284999162758223, 371284999010740279, 371284998857866304, 371284998795109298, 371284998194651108, 371284997593713005]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 49770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 49700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362496346134486165, 362496381943392109⟩, ⟨(-568107865426335469), (-566903323008153161)⟩, true⟩

def words08 : List Nat := [371284996992072983, 371284996734344589, 371284996273997949, 371284996217050639, 371284996159542736, 371284996032944775, 371284995640105821, 371284995646425187, 371284996054478201, 371284996284879363]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 49780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 49700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486297817668715, 362486333641741870⟩, ⟨(-67765648311855615), (-66560350643204291)⟩, true⟩

def words09 : List Nat := [371284996433612129, 371284996582901110, 371284996862349006, 371284996963024424, 371284997108344813, 371284997254278346, 371284997323996672, 371284997325687058, 371284997086441422, 371284997115353983]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 49790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 49700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 49700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk497
