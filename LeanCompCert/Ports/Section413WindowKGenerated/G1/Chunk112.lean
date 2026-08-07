import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk112

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362460110890106986, 362460112485656531⟩, ⟨290814727256005084, 290826823459739920⟩, true⟩

def state01 : KState := ⟨⟨362479313550188940, 362479315148692552⟩, ⟨75917193811406587, 75929323116160149⟩, true⟩

def words00 : List Nat := [371286080145299263, 371286080145662591, 371286083833705093, 371286088202391775, 371286091468904825, 371286091469236634, 371286087247556254, 371286086332111670, 371286088504560165, 371286088504902736]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 11200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 11200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362508718680861059, 362508720282374973⟩, ⟨(-253697514529674863), (-253685351464250679)⟩, true⟩

def words01 : List Nat := [371286087900979985, 371286086159260470, 371286090606321678, 371286094015361287, 371286099787861822, 371286105559462889, 371286111341813794, 371286111342144542, 371286110179340484, 371286112194730000]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 11210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 11200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362436690354330320, 362436691958793446⟩, ⟨554815494499790025, 554827690670687183⟩, true⟩

def words02 : List Nat := [371286117061157303, 371286117061488510, 371286113261443633, 371286108710471140, 371286104160180570, 371286102040964479, 371286096578594495, 371286097200746370, 371286097808020791, 371286097808363410]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 11220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 11200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362532356787243563, 362532358394705633⟩, ⟨(-520108747699955042), (-520096517836030104)⟩, true⟩

def words03 : List Nat := [371286093409529701, 371286093013934018, 371286098570616833, 371286098570948309, 371286095661551932, 371286090797821914, 371286086119106632, 371286086119471463, 371286086462139068, 371286090578867538]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 11230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 11200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477716079267844, 362477717689730283⟩, ⟨94472011668901060, 94484275272169732⟩, true⟩

def words04 : List Nat := [371286094663592061, 371286094780824859, 371286102784033455, 371286110785985325, 371286120179032978, 371286120179364818, 371286119065553888, 371286117043119897, 371286116291595033, 371286116291976699]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 11240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 11200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362495672017516344, 362495673630965604⟩, ⟨(-107311371657623472), (-107299074437312766)⟩, true⟩

def words05 : List Nat := [371286122675608035, 371286129804579504, 371286135806601394, 371286135806934283, 371286134176995508, 371286134533192038, 371286142758091410, 371286143558896471, 371286144405512947, 371286145252097181]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 11250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 11200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362564669072752012, 362564670689180336⟩, ⟨(-884414039054314171), (-884401708274520867)⟩, true⟩

def words06 : List Nat := [371286153964010702, 371286158740091547, 371286166804776664, 371286174868167277, 371286181697730282, 371286181698062790, 371286183340701408, 371286186918967720, 371286196712940523, 371286203675758766]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 11260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 11200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362548857190863601, 362548858810321663⟩, ⟨(-705990701917356971), (-705978336976901437)⟩, true⟩

def words07 : List Nat := [371286210123761218, 371286216570732215, 371286230865267615, 371286241232416410, 371286250950228580, 371286260666438834, 371286268821489433, 371286268821822004, 371286272077904888, 371286277626297472]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 11270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 11200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362511593328229309, 362511594950653916⟩, ⟨(-285420905951109968), (-285408507532922760)⟩, true⟩

def words08 : List Nat := [371286288878786445, 371286289690305398, 371286290501146159, 371286291311959817, 371286293182179338, 371286293182552381, 371286300449924185, 371286307997417872, 371286315188792039, 371286317428066641]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 11280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 11200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362559419219119269, 362559420844554139⟩, ⟨(-825766743716548154), (-825754311296898002)⟩, true⟩

def words09 : List Nat := [371286322943038581, 371286328457197289, 371286339499910779, 371286340123913928, 371286340124174290, 371286339435344727, 371286340119550282, 371286340119923159, 371286345241413469, 371286351708079766]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 11290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 11200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 11200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk112
