import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk295

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360553532169411417, 360553537395945828⟩, ⟨882319781383298801, 882424055260492741⟩, true⟩

def state01 : KState := ⟨⟨360625643101968486, 360625648332190098⟩, ⟨(-1245204724780809988), (-1245100342112642780)⟩, true⟩

def words00 : List Nat := [360583449193868084, 360583450253752930, 360583452171516148, 360583454089223962, 360583454952299051, 360583454952689830, 360583454888345405, 360583455104256069, 360583455843064351, 360583457273191330]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 29500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 29500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360570997492828219, 360571002726778148⟩, ⟨367757845595274041, 367862338304909005⟩, true⟩

def words01 : List Nat := [360583458130509791, 360583458987817246, 360583460012506189, 360583461618007462, 360583462936783774, 360583464255534508, 360583465003530415, 360583465003921335, 360583464609803749, 360583464188102841]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 29510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 29500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593436614431868, 360593441852064801⟩, ⟨(-294809793627907549), (-294705192177849885)⟩, true⟩

def words02 : List Nat := [360583464095215269, 360583464095606574, 360583463835193709, 360583462841384301, 360583461847576308, 360583460545162563, 360583461097666800, 360583461945662897, 360583461994153308, 360583462332503058]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 29520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 29500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360637513899333969, 360637519140663695⟩, ⟨(-1596757891791990841), (-1596653181157415337)⟩, true⟩

def words03 : List Nat := [360583463813626744, 360583465294765029, 360583466748408801, 360583467061442363, 360583467061805369, 360583466263766171, 360583465809766578, 360583466762361432, 360583468592480903, 360583470422571640]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 29530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 29500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360608402902353274, 360608408147408478⟩, ⟨(-736956043498782430), (-736851222795617906)⟩, true⟩

def words04 : List Nat := [360583471531051851, 360583471531443150, 360583472138948750, 360583472778587333, 360583472846622264, 360583473382785679, 360583473383143816, 360583472946333919, 360583472509480308, 360583473247648889]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 29540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 29500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360541515677597300, 360541520926335773⟩, ⟨1240111812663457514, 1240216742226291258⟩, true⟩

def words05 : List Nat := [360583474696402038, 360583476145131617, 360583477024780287, 360583477941089901, 360583478220367518, 360583478499733082, 360583478947573202, 360583478947964743, 360583478256768137, 360583476837777800]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 29550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 29500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360558321673318075, 360558326925760109⟩, ⟨743033366960520476, 743138406018894182⟩, true⟩

def words06 : List Nat := [360583475418800796, 360583473560710319, 360583472440809264, 360583471128920087, 360583469817091993, 360583467537045683, 360583464118396332, 360583461840193634, 360583459562020463, 360583458424103664]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 29560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 29500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360541147903837110, 360541153160008517⟩, ⟨1251026899446768188, 1251132048800814450⟩, true⟩

def words07 : List Nat := [360583457574582988, 360583456156709428, 360583454738857008, 360583454881785210, 360583454882120766, 360583454357926760, 360583453833725560, 360583452741554498, 360583451142886661, 360583449713382446]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 29570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 29500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585826042748951, 360585831302614940⟩, ⟨(-70772922960173790), (-70667664301796206)⟩, true⟩

def words08 : List Nat := [360583448283844057, 360583447993540890, 360583447738855038, 360583446787259741, 360583445835664969, 360583444318490933, 360583443577133632, 360583443776076021, 360583443776431240, 360583443155397821]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 29580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 29500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360634602005743222, 360634607269305375⟩, ⟨(-1514390845339315940), (-1514285477292708392)⟩, true⟩

def words09 : List Nat := [360583444081200557, 360583445007059552, 360583446760436128, 360583447377495395, 360583447377856834, 360583447009878922, 360583446655962777, 360583447247050861, 360583448975747240, 360583450704415922]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 29590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 29500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 29500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk295
