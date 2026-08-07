import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk320

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362477626429368414, 362477640695327042⟩, ⟨236858246950174108, 237166806459732238⟩, true⟩

def state01 : KState := ⟨⟨362465707438940837, 362465721714197034⟩, ⟨618198320145209882, 618507177224324046⟩, true⟩

def words00 : List Nat := [371285051927198783, 371285051701076738, 371285050176166214, 371285049623767270, 371285049070873651, 371285048669955283, 371285047335385063, 371285045908149033, 371285044480574644, 371285044025263086]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 32000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 32000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362434594493552048, 362434608778091340⟩, ⟨1614283813728735049, 1614592968007273781⟩, true⟩

def words01 : List Nat := [371285043422362513, 371285042966157143, 371285042509648970, 371285042047823341, 371285040288045744, 371285038721111849, 371285037153726388, 371285036415190797, 371285034866702274, 371285033293019738]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 32010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 32000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362450219004767294, 362450233298528991⟩, ⟨1113896044583830725, 1114205494211480977⟩, true⟩

def words02 : List Nat := [371285031718992498, 371285030391792353, 371285028582230618, 371285027589604549, 371285026596725618, 371285025340093326, 371285022935904218, 371285021503182989, 371285020070025954, 371285019608057917]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 32020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 32000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362441002260063129, 362441016563262722⟩, ⟨1409276564922369486, 1409586316891045802⟩, true⟩

def words03 : List Nat := [371285018522816701, 371285017433386195, 371285016343557854, 371285016101120412, 371285015501311408, 371285015078361482, 371285014655099650, 371285014162053205, 371285012514300152, 371285011142441594]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 32030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 32000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362426209129011522, 362426223441406158⟩, ⟨1883371571958559394, 1883681618584523456⟩, true⟩

def words04 : List Nat := [371285009770071064, 371285009317443621, 371285007748183203, 371285005978383757, 371285004208315530, 371285002434994054, 371285000334304480, 371284999108268029, 371284997881954781, 371284996658834693]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 32040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 32000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490513390604355, 362490527712333740⟩, ⟨(-177933734809358252), (-177623388956743354)⟩, true⟩

def words05 : List Nat := [371284994825795193, 371284993962960740, 371284993099671494, 371284992475447962, 371284991232849459, 371284989829298689, 371284988425407228, 371284987991374785, 371284987368401726, 371284987542377821]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 32050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 32000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475736955923902, 362475751286963504⟩, ⟨295834250212257931, 296144894598354455⟩, true⟩

def words06 : List Nat := [371284987718914666, 371284987719952453, 371284987610409841, 371284988041026434, 371284988506026632, 371284988507059845, 371284987678319479, 371284986667655694, 371284985656644847, 371284985614827501]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 32060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 32000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475496471022243, 362475510811382037⟩, ⟨303682009107262815, 303992952438278083⟩, true⟩

def words07 : List Nat := [371284985687126439, 371284986047764510, 371284986411397337, 371284986412449699, 371284986226969571, 371284986278227933, 371284987297010422, 371284987298044447, 371284987195146238, 371284986900921884]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 32070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 32000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488809753431551, 362488824103051166⟩, ⟨(-123428300477273406), (-123117060043704154)⟩, true⟩

def words08 : List Nat := [371284986715150043, 371284986716288537, 371284986929590607, 371284987520876125, 371284987930707320, 371284987931741364, 371284987198021341, 371284986971568170, 371284987484341903, 371284987604966230]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 32080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 32000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362501285688504240, 362501300047531430⟩, ⟨(-523851902504385638), (-523540360134238832)⟩, true⟩

def words09 : List Nat := [371284987671681082, 371284987738729543, 371284988630994624, 371284989041348640, 371284989477193937, 371284989913412222, 371284990326819709, 371284990327860817, 371284990377721949, 371284990887064958]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 32090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 32000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 32000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk320
