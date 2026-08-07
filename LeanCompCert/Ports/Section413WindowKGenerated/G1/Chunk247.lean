import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk247

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487100820682206, 362487109137541484⟩, ⟨(-33981109849090250), (-33842217674834038)⟩, true⟩

def state01 : KState := ⟨⟨362524862717333709, 362524871041174481⟩, ⟨(-966911529263274215), (-966772464610595345)⟩, true⟩

def words00 : List Nat := [371285740134554642, 371285740537794344, 371285741607234588, 371285742676905658, 371285743429831416, 371285743430615759, 371285743370503581, 371285744013233650, 371285746294720322, 371285747878833395]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 24700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 24700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362517270452643575, 362517278783589846⟩, ⟨(-779203138678048441), (-779063898412304913)⟩, true⟩

def words01 : List Nat := [371285749454352097, 371285751030012107, 371285753681355796, 371285755513233166, 371285757832492880, 371285760151855634, 371285761891501579, 371285761977261353, 371285763252743870, 371285764528567303]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 24710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 24700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495156483853668, 362495164821744437⟩, ⟨(-232385090469690098), (-232245678499734384)⟩, true⟩

def words02 : List Nat := [371285767092818817, 371285767813008883, 371285768271942659, 371285768731103050, 371285769323573545, 371285769324436528, 371285770728825697, 371285772151961081, 371285773568268317, 371285773948811692]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 24720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 24700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362521231201962659, 362521239546911704⟩, ⟨(-877317997842947898), (-877178411286479444)⟩, true⟩

def words03 : List Nat := [371285774996652397, 371285776044802489, 371285778727726205, 371285779482362577, 371285779676175304, 371285779870223390, 371285781256990769, 371285782234730578, 371285783668464710, 371285785102415262]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 24730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 24700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489956213923748, 362489964565914435⟩, ⟨(-103574607872787820), (-103434847070090000)⟩, true⟩

def words04 : List Nat := [371285786543434182, 371285786544215042, 371285786951806704, 371285787854165923, 371285788731883125, 371285788732663975, 371285787435555902, 371285786205980780, 371285785379269013, 371285785549023397]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 24740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 24700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362444808970191136, 362444817329227868⟩, ⟨1014252025657060128, 1014391960885190022⟩, true⟩

def words05 : List Nat := [371285787113443989, 371285788678085488, 371285790010993532, 371285790011774581, 371285789171034425, 371285788818491135, 371285789300309735, 371285789301090914, 371285787963704524, 371285786309877513]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 24750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 24700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488507222311578, 362488515588345327⟩, ⟨(-67832045552385408), (-67691937042987864)⟩, true⟩

def words06 : List Nat := [371285784655834797, 371285783823283390, 371285782179620026, 371285782167477738, 371285782155103890, 371285781964058358, 371285781193172039, 371285781623698821, 371285782768116063, 371285782879248279]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 24760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 24700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489010752180172, 362489019125336397⟩, ⟨(-80328897890295746), (-80188612920937076)⟩, true⟩

def words07 : List Nat := [371285782879834094, 371285782847075617, 371285783447323765, 371285783448184764, 371285783577951264, 371285783884622594, 371285784201425537, 371285784202211090, 371285783102855486, 371285783234415089]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 24770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 24700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362459680926035061, 362459689306152181⟩, ⟨646681409299606195, 646821866796414351⟩, true⟩

def words08 : List Nat := [371285784994532635, 371285784995314826, 371285784586797314, 371285783876537711, 371285783166027044, 371285782942453138, 371285782046818681, 371285781818595317, 371285781590134465, 371285781354026180]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 24780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 24700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362560050776139741, 362560059163337941⟩, ⟨(-1841992562821812651), (-1841851929749780881)⟩, true⟩

def words09 : List Nat := [371285780320760222, 371285780340381243, 371285781986645528, 371285782895120643, 371285783646096063, 371285784397239151, 371285786574689966, 371285787944134258, 371285790939473058, 371285793934929822]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 24790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 24700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 24700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk247
