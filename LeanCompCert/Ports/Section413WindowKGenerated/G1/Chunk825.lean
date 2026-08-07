import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk825

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493624403971222, 362493726706364728⟩, ⟨(-703551443038367572), (-697852487359090700)⟩, true⟩

def state01 : KState := ⟨⟨362488180540308385, 362488282868159546⟩, ⟨(-254391661243040525), (-248690605172271641)⟩, true⟩

def words00 : List Nat := [371285268152359174, 371285268210297075, 371285268260388974, 371285268311450446, 371285268384473009, 371285268387624237, 371285268532007864, 371285268679790678, 371285268798961079, 371285268838452328]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496964137861672, 362497066491600900⟩, ⟨(-979194798631802794), (-973491606407102260)⟩, true⟩

def words01 : List Nat := [371285268917972553, 371285268999025873, 371285269213555552, 371285269233196472, 371285269235409595, 371285269231588798, 371285269294792521, 371285269305088854, 371285269449990097, 371285269596187526]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489495527477247, 362489597907087497⟩, ⟨(-362888707071910877), (-357183379841121051)⟩, true⟩

def words02 : List Nat := [371285269737450010, 371285269768483134, 371285269858779049, 371285269950512086, 371285270083765066, 371285270086625134, 371285270024256329, 371285269962660390, 371285269982012988, 371285270037803942]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472147161460211, 362472249566768134⟩, ⟨1069026731936498879, 1074734180128899641⟩, true⟩

def words03 : List Nat := [371285270239067462, 371285270441465320, 371285270594139238, 371285270597002107, 371285270593312136, 371285270600104620, 371285270640984038, 371285270643844495, 371285270489205963, 371285270334639820]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482523014785226, 362482625445708761⟩, ⟨212575139963644237, 218284702597448349⟩, true⟩

def words04 : List Nat := [371285270178831203, 371285270142322456, 371285270055625571, 371285270083081330, 371285270085844175, 371285270088704990, 371285269910684991, 371285269798254297, 371285269715322877, 371285269718302310]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486469600856143, 362486572057896727⟩, ⟨(-113250894200570019), (-107539175473779605)⟩, true⟩

def words05 : List Nat := [371285269688446405, 371285269631912601, 371285269636051721, 371285269639204659, 371285269629918082, 371285269623606689, 371285269616375592, 371285269609770430, 371285269496463876, 371285269515831179]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482791371788546, 362482893854297309⟩, ⟨190455612984381742, 196169434496711928⟩, true⟩

def words06 : List Nat := [371285269680343317, 371285269683204482, 371285269652339370, 371285269619070932, 371285269584769088, 371285269554076143, 371285269533452324, 371285269598686556, 371285269646831478, 371285269649798057]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497373879108704, 362497476387490957⟩, ⟨(-1013646785474171563), (-1007930827455673305)⟩, true⟩

def words07 : List Nat := [371285269740956576, 371285269862396803, 371285270110510718, 371285270239478042, 371285270341822104, 371285270445083778, 371285270621911020, 371285270726803654, 371285270876583384, 371285271027572142]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494143713991986, 362494246248192323⟩, ⟨(-746917666803279753), (-741199576596974923)⟩, true⟩

def words08 : List Nat := [371285271177238419, 371285271180100532, 371285271247348421, 371285271349977465, 371285271495874387, 371285271547638136, 371285271598361131, 371285271650044319, 371285271797940491, 371285271909867361]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485082016153766, 362485184576183910⟩, ⟨1596121223393571, 7316344841361869⟩, true⟩

def words09 : List Nat := [371285272167148067, 371285272425631081, 371285272650952033, 371285272702155461, 371285272797308057, 371285272893843125, 371285273117868540, 371285273147401574, 371285273149556215, 371285273151787317]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk825
