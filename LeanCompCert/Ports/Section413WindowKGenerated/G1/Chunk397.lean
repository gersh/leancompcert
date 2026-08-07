import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk397

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362445559524620352, 362445581875868496⟩, ⟨1573241356871171532, 1573840976100906020⟩, true⟩

def state01 : KState := ⟨⟨362476182147825339, 362476204510716024⟩, ⟨357376676332298398, 357976757830683260⟩, true⟩

def words00 : List Nat := [371285224227728500, 371285223584949626, 371285222704854191, 371285222459461278, 371285222213639886, 371285221863338217, 371285220667842440, 371285219996447150, 371285219324412440, 371285219286788316]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 39700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 39700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489005896790133, 362489028271552756⟩, ⟨(-151943161947453302), (-151342608954083238)⟩, true⟩

def words01 : List Nat := [371285219060769217, 371285218722649054, 371285218596737991, 371285218598171313, 371285218494856181, 371285218490096771, 371285218484920341, 371285218473929250, 371285218033048203, 371285218130595729]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 39710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 39700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362457473733988458, 362457496120340072⟩, ⟨1100642737026173837, 1101243750394590001⟩, true⟩

def words02 : List Nat := [371285218402106620, 371285218403408082, 371285217830868687, 371285217258867765, 371285216686426437, 371285216111562567, 371285215220927782, 371285214964246724, 371285214707120958, 371285214311892919]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 39720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 39700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487041914097767, 362487064312207742⟩, ⟨(-74201605472198604), (-73600124884541994)⟩, true⟩

def words03 : List Nat := [371285213615129987, 371285213438189692, 371285213715185818, 371285213716487822, 371285213328505152, 371285212840664737, 371285212429600523, 371285212431035575, 371285212269366482, 371285212317419374]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 39730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 39700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482604768125717, 362482627177994164⟩, ⟨102036683448513370, 102638631375698886⟩, true⟩

def words04 : List Nat := [371285212355423484, 371285212356726794, 371285211686284522, 371285211339757276, 371285210992567206, 371285210838376172, 371285210290570388, 371285209743632320, 371285209280441067, 371285209281928144]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 39740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 39700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362483337036482733, 362483359458104560⟩, ⟨73041100543456446, 73643515727575818⟩, true⟩

def words05 : List Nat := [371285209713563177, 371285210210671181, 371285210580654610, 371285210581972334, 371285210761206132, 371285210948239828, 371285211707861128, 371285211709164126, 371285211704283707, 371285211659204349]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 39750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 39700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488730671282668, 362488753104555586⟩, ⟨(-141343384713149333), (-140740506221351701)⟩, true⟩

def words06 : List Nat := [371285212199038101, 371285212514967814, 371285213227200468, 371285213939912842, 371285214462813117, 371285214464116534, 371285214229258725, 371285214023666815, 371285214242099069, 371285214332429632]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 39760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 39700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495587553942984, 362495609999097027⟩, ⟨(-414043303073665580), (-413439952012108212)⟩, true⟩

def words07 : List Nat := [371285214425876853, 371285214519737736, 371285215137487740, 371285215526600076, 371285215998350360, 371285216470601772, 371285216943017882, 371285216944321555, 371285216836284591, 371285217099169622]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 39770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 39700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468658411254085, 362468680868023208⟩, ⟨657314545620682701, 657918358790594435⟩, true⟩

def words08 : List Nat := [371285217621521804, 371285217622825540, 371285217303780777, 371285216940234215, 371285216576195833, 371285216386158424, 371285215955677198, 371285215849127312, 371285215742137796, 371285215634517066]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 39780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 39700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362506264262157285, 362506286730724580⟩, ⟨(-839215304792490113), (-838611022113873395)⟩, true⟩

def words09 : List Nat := [371285215435380636, 371285215652465906, 371285216286695571, 371285216287999896, 371285216153833086, 371285215860934383, 371285215670116928, 371285215671578318, 371285216100549955, 371285216631427732]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 39790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 39700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 39700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk397
