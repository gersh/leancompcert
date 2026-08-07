import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk423

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492378474179779, 362492403979648098⟩, ⟨(-306223223258013735), (-305494233750303723)⟩, true⟩

def state01 : KState := ⟨⟨362484904444113146, 362484929962004246⟩, ⟨9968508620993622, 10698023677832140⟩, true⟩

def words00 : List Nat := [371285182466248337, 371285182467647986, 371285182338408757, 371285182158211960, 371285181977471348, 371285181964990982, 371285182107487976, 371285182459305906, 371285182809148208, 371285182810590345]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 42300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 42300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498606631349518, 362498632161847340⟩, ⟨(-569850850725931324), (-569120802216225086)⟩, true⟩

def words01 : List Nat := [371285183210407510, 371285183616914750, 371285184244660691, 371285184246054186, 371285184129703114, 371285183976093525, 371285183952933034, 371285183954482495, 371285184126182650, 371285184445531180]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 42310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 42300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483494177740867, 362483519720822037⟩, ⟨69787227699422980, 70517808800867854⟩, true⟩

def words02 : List Nat := [371285184762928679, 371285184764346630, 371285185031049613, 371285185444871403, 371285186030026602, 371285186031420553, 371285185872841798, 371285185714473726, 371285185625413015, 371285185627006797]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 42320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 42300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472728367972544, 362472753923600046⟩, ⟨525687145258750206, 526418257507168292⟩, true⟩

def words03 : List Nat := [371285186107646478, 371285186628172876, 371285187123726872, 371285187125121545, 371285186958350845, 371285186959595128, 371285187517843629, 371285187519238117, 371285187334679541, 371285187042577542]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 42330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 42300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479373752849861, 362479399320969985⟩, ⟨244267689687751164, 244999330937744026⟩, true⟩

def words04 : List Nat := [371285186819482792, 371285186821019026, 371285186613441144, 371285186541842906, 371285186469811731, 371285186301245304, 371285185509271299, 371285184963479167, 371285184427658217, 371285184429138527]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 42340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 42300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481742142107920, 362481767722934132⟩, ⟨143988300767987506, 144720480186209856⟩, true⟩

def words05 : List Nat := [371285184293584621, 371285184147110230, 371285184274889749, 371285184346300291, 371285184560218644, 371285184774647401, 371285184879944498, 371285184881339646, 371285184243779966, 371285184164864874]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 42350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 42300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362461709664967648, 362461735258225890⟩, ⟨992669545344098388, 993402251446667860⟩, true⟩

def words06 : List Nat := [371285184289960470, 371285184291355984, 371285183833869156, 371285183374372800, 371285182914347577, 371285182534853003, 371285181923721374, 371285181676188456, 371285181428177722, 371285181145680379]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 42360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 42300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495313863403448, 362495339469278955⟩, ⟨(-431361926577342108), (-430628685817523060)⟩, true⟩

def words07 : List Nat := [371285180593296564, 371285180270724589, 371285180180651917, 371285180182047731, 371285179674144575, 371285179101932977, 371285178529169918, 371285178414586367, 371285178337801618, 371285178579120216]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 42370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 42300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362446179553371878, 362446205171841588⟩, ⟨1651135777049593645, 1651869551616278683⟩, true⟩

def words08 : List Nat := [371285178749817418, 371285178751213525, 371285178179888785, 371285177894790591, 371285177609015715, 371285177343157497, 371285176335204355, 371285175332333652, 371285174328959184, 371285173550034943]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 42380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 42300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362461087195840857, 362461112826916660⟩, ⟨1019226524186475807, 1019960833188697213⟩, true⟩

def words09 : List Nat := [371285172631721918, 371285172271006211, 371285171909803001, 371285171549352843, 371285170815005843, 371285170203643182, 371285169591602277, 371285169536885665, 371285169072718387, 371285168506944696]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 42390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 42300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 42300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk423
