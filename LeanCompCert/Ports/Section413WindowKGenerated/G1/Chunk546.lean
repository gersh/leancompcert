import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk546

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473058998460299, 362473102381299741⟩, ⟨642416439576525489, 644016606083062645⟩, true⟩

def state01 : KState := ⟨⟨362462007416364116, 362462050815535409⟩, ⟨1245951129222028605, 1247552187532604559⟩, true⟩

def words00 : List Nat := [371284897461529350, 371284897463366791, 371284897222922495, 371284896982272218, 371284896740926814, 371284896567831297, 371284896267795965, 371284896039596521, 371284895810762875, 371284895572677556]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 54600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 54600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497641937037109, 362497685352767944⟩, ⟨(-700235761716874617), (-698633799005539221)⟩, true⟩

def words01 : List Nat := [371284895155605240, 371284895012294078, 371284894944726519, 371284894946594635, 371284894803364035, 371284894555082937, 371284894390672594, 371284894392695172, 371284894545176212, 371284894781394196]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 54610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 54600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362493968555167063, 362494011987513455⟩, ⟨(-499664139090661348), (-498061268753395190)⟩, true⟩

def words02 : List Nat := [371284894918869061, 371284894920706269, 371284894772385277, 371284894867243058, 371284894985953984, 371284894987811135, 371284894907842196, 371284894825716671, 371284894993477154, 371284895162473581]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 54620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 54600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481211889125100, 362481255338001977⟩, ⟨197383317908295244, 198987091391476426⟩, true⟩

def words03 : List Nat := [371284895665359980, 371284896168990293, 371284896672173440, 371284896776132753, 371284896877922968, 371284896980575415, 371284897253343550, 371284897255184892, 371284897186816304, 371284897122251455]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 54630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 54600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362492186105174512, 362492229570514150⟩, ⟨(-402206085556668454), (-400601412467111972)⟩, true⟩

def words04 : List Nat := [371284897272316098, 371284897369251285, 371284897751734748, 371284898134937885, 371284898464202411, 371284898466039256, 371284898651034710, 371284898912435998, 371284899259142097, 371284899395174868]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 54640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 54600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362478902951015605, 362478946433067579⟩, ⟨323829084079306827, 325434670584077109⟩, true⟩

def words05 : List Nat := [371284899530924036, 371284899667280378, 371284899972811497, 371284900111750151, 371284900279776473, 371284900448557464, 371284900615916299, 371284900617753320, 371284900339055476, 371284900232383058]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 54650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 54600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475157071258620, 362475200569692429⟩, ⟨528578741456863171, 530185223478646743⟩, true⟩

def words06 : List Nat := [371284900298221402, 371284900300058696, 371284900066569274, 371284899767553096, 371284899467836199, 371284899204945325, 371284898774626367, 371284898679379540, 371284898583533097, 371284898488541499]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 54660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 54600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496757294671838, 362496800809716218⟩, ⟨(-652414903321829694), (-650807513116284166)⟩, true⟩

def words07 : List Nat := [371284898373765979, 371284898437355645, 371284898834210136, 371284898836047882, 371284898787439502, 371284898686273884, 371284898590668384, 371284898592703034, 371284898695106001, 371284898914851160]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 54670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 54600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481620475294870, 362481664006924021⟩, ⟨175300812765939915, 176909109910754189⟩, true⟩

def words08 : List Nat := [371284899071426831, 371284899073268858, 371284898981417280, 371284899082000728, 371284899283720146, 371284899285559309, 371284899103467666, 371284898922320486, 371284898766391216, 371284898768487575]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 54680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 54600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477220562842249, 362477264111021435⟩, ⟨415964209935875456, 417573412286104976⟩, true⟩

def words09 : List Nat := [371284898727356536, 371284898746087097, 371284898747474987, 371284898734424944, 371284898464848208, 371284898298357600, 371284898268471145, 371284898270341757, 371284898131756011, 371284897994244216]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 54690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 54600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 54600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk546
