import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk001

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨352776791864166943, 352776791864237312⟩, ⟨949360578249322069, 949360578254156953⟩, true⟩

def state01 : KState := ⟨⟨366105063886224669, 366105063886310698⟩, ⟨(-432594447703902726), (-432594447697419342)⟩, true⟩

def words00 : List Nat := [370976401549923147, 370969099813602017, 370961378462758173, 370999361964757886, 371014392221112104, 371014392221113873, 370923232203593430, 370913356235336169, 370972387089059523, 371007816609757371]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362527100297796990, 362527100297901201⟩, ⟨14211163092622812, 14211163101202292⟩, true⟩

def words01 : List Nat := [371035305855247100, 371062308565419087, 371162761216590972, 371231957289705555, 371309607445374440, 371385930247955672, 371460336269723367, 371460336269725400, 371446521836564230, 371445526657077887]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨359171643739815313, 359171643739938708⟩, ⟨426453319877577330, 426453319888561260⟩, true⟩

def words02 : List Nat := [371478553653745305, 371478553653747390, 371431187710613382, 371378943611875312, 371327535418716339, 371296343581357949, 371246614225856918, 371250309487422386, 371252053892925369, 371252053892927641]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨368570602002726906, 368570602002871498⟩, ⟨(-850291704123072588), (-850291704109222680)⟩, true⟩

def words03 : List Nat := [371256071140784343, 371284692716892360, 371328427127941972, 371328427127944285, 371304560491272569, 371272399401070598, 371258233042211996, 371258233042214607, 371297089830660031, 371340164385075593]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨357899045501459852, 357899045501627700⟩, ⟨669527995191957094, 669527995209186418⟩, true⟩

def words04 : List Nat := [371380730346404041, 371380730346406547, 371360440060460115, 371355184552273228, 371354028255408909, 371354028255411508, 371301642822197336, 371240963951956581, 371181099563194594, 371162565469688943]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨359237836909244708, 359237836909437406⟩, ⟨493021652606164969, 493021652627253011⟩, true⟩

def words05 : List Nat := [371143880683368703, 371154613475746951, 371160029321805528, 371160029321808277, 371141632192399982, 371134372396567277, 371157568380777198, 371157568380780030, 371138602020297389, 371119222238357738]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360758598831084959, 360758598831304295⟩, ⟨245659549134908972, 245659549160398872⟩, true⟩

def words06 : List Nat := [371100083199049679, 371091380756259062, 371070826011425769, 371077717463760644, 371077717463762939, 371073508331237246, 371024979313484239, 371009982953188509, 371003655002832887, 371003655002836054]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361883880311310925, 361883880311559224⟩, ⟨57276295562927706, 57276295593492280⟩, true⟩

def words07 : List Nat := [370995204381952247, 370985864987897553, 370998819844444057, 371007469702963682, 371017626168328817, 371027667871374688, 371035279762805020, 371035279762808252, 371003859616546811, 371002081953745293]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨359924004599821434, 359924004600100203⟩, ⟨447367531182731788, 447367531218942114⟩, true⟩

def words08 : List Nat := [371027571906484077, 371036645687079281, 371043957554389976, 371051190374487672, 371063743865655853, 371063743865659584, 371070400312137803, 371077248198736007, 371078570553880471, 371078570553884109]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨371132091258236268, 371132091258547978⟩, ⟨(-1738994481489300173), (-1738994481446662291)⟩, true⟩

def words09 : List Nat := [371080125501309020, 371093864158885647, 371133283194838080, 371139173931108167, 371142581829489821, 371145955129919511, 371174322186749785, 371193425522628411, 371237118851310546, 371280377420504883]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk001
