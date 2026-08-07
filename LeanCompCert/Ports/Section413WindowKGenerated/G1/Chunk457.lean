import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk457

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485125294178888, 362485155252101913⟩, ⟨16223211540518405, 17148214598999065⟩, true⟩

def state01 : KState := ⟨⟨362493817710105124, 362493847681593795⟩, ⟨(-381057368407590654), (-380131745329423094)⟩, true⟩

def words00 : List Nat := [371285530808842526, 371285530901477828, 371285531192686575, 371285531484494266, 371285531635124595, 371285531636638945, 371285531149428408, 371285531141296337, 371285531518429782, 371285531701953678]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 45700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 45700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487515330174979, 362487545315482579⟩, ⟨(-92906457299071685), (-91980202488092403)⟩, true⟩

def words01 : List Nat := [371285531885960298, 371285532070477188, 371285532555325295, 371285532861347599, 371285533214147279, 371285533567507221, 371285533828796944, 371285533830311848, 371285533498123709, 371285533544032084]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 45710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 45700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362466214050247484, 362466244049050147⟩, ⟨881103366715878257, 882030238591750303⟩, true⟩

def words02 : List Nat := [371285533902549995, 371285533904064977, 371285533625459428, 371285533347076393, 371285533068111788, 371285532863350127, 371285532419227013, 371285532223192381, 371285532026645310, 371285531830344522]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 45720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 45700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362494303764958971, 362494333777464194⟩, ⟨(-403652274838239758), (-402724776274866240)⟩, true⟩

def words03 : List Nat := [371285531409625431, 371285531141838164, 371285530873297699, 371285530841549944, 371285530354309921, 371285529792231588, 371285529229549240, 371285529145182000, 371285529123912168, 371285529318089129]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 45730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 45700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362462491725676287, 362462521751845021⟩, ⟨1051554012530614311, 1052482136132856523⟩, true⟩

def words04 : List Nat := [371285529521059658, 371285529522575452, 371285529088761375, 371285529068627142, 371285529047879837, 371285529049395884, 371285528475150108, 371285527843065352, 371285527210413457, 371285526825858854]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 45740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 45700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362451113250853630, 362451143290716708⟩, ⟨1572282781060709012, 1573211531244323528⟩, true⟩

def words05 : List Nat := [371285526324055785, 371285526300227055, 371285526275842508, 371285526211060547, 371285525509485823, 371285524953592673, 371285524396937534, 371285524317964208, 371285523662914992, 371285522913340055]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 45750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 45700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490493515736138, 362490523569153263⟩, ⟨(-229900917825233480), (-228971547338455608)⟩, true⟩

def words06 : List Nat := [371285522163082981, 371285521825088960, 371285521297372367, 371285521247348253, 371285521196876737, 371285521091228136, 371285520596111866, 371285520578815170, 371285520911969817, 371285521022839256]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 45760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 45700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485314693201781, 362485344760440864⟩, ⟨7133267826716526, 8063271015195296⟩, true⟩

def words07 : List Nat := [371285521061873078, 371285521101392352, 371285521258793651, 371285521260480103, 371285521242991961, 371285521307677618, 371285521371323442, 371285521372840759, 371285520893260741, 371285520891306203]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 45770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 45700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474737397510069, 362474767478249240⟩, ⟨491456426450330322, 492387047744187560⟩, true⟩

def words08 : List Nat := [371285521185250339, 371285521186777650, 371285521056648070, 371285520927123366, 371285520810586973, 371285520812266336, 371285520647343709, 371285520643572737, 371285520639304357, 371285520635002772]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 45780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 45700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497854624003510, 362497884718483808⟩, ⟨(-567200379229205940), (-566269128662539772)⟩, true⟩

def words09 : List Nat := [371285520521085468, 371285520642819098, 371285520907195418, 371285520908739369, 371285520777741332, 371285520571507057, 371285520523918552, 371285520525595205, 371285520761989375, 371285521033658968]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 45790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 45700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 45700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk457
