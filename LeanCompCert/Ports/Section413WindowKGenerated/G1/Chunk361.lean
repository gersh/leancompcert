import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk361

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362454556796307374, 362454575134305022⟩, ⟨1097625692015626342, 1098073085965852796⟩, true⟩

def state01 : KState := ⟨⟨362501948786840388, 362501967135347824⟩, ⟨(-613442733463188570), (-612994960055597676)⟩, true⟩

def words00 : List Nat := [371284991829545476, 371284991499278918, 371284990974563482, 371284991055958317, 371284991056868053, 371284991014228908, 371284990423278183, 371284990512085335, 371284991366751320, 371284991838068447]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 36100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 36100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482830868113885, 362482849227349033⟩, ⟨77021770889619065, 77469931727451107⟩, true⟩

def words01 : List Nat := [371284992306909241, 371284992776136269, 371284993279817870, 371284993499983414, 371284993898550922, 371284994297534376, 371284994698079798, 371284994699254844, 371284994078477245, 371284994020586228]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 36110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 36100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362444058350694788, 362444076720392756⟩, ⟨1477740460979839869, 1478188999789528743⟩, true⟩

def words02 : List Nat := [371284994477070956, 371284994478246072, 371284993973228177, 371284993466711198, 371284992959778297, 371284992522881691, 371284991711768202, 371284991070019728, 371284990427894208, 371284989784322719]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 36120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 36100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362508401105346322, 362508419485649490⟩, ⟨(-847272792205681602), (-846823870175718386)⟩, true⟩

def words03 : List Nat := [371284988652767016, 371284988287269340, 371284988099536463, 371284988100733360, 371284987798831759, 371284987308050008, 371284987089919317, 371284987091216827, 371284987722569512, 371284988372227734]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 36130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 36100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362501808511432325, 362501826902360748⟩, ⟨(-609073781772678002), (-608624475692106836)⟩, true⟩

def words04 : List Nat := [371284988874896656, 371284988876075695, 371284988962494951, 371284989326852525, 371284989923758752, 371284990001750808, 371284990077694063, 371284990154040951, 371284990815937251, 371284991282994974]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 36140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 36100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362465319135470021, 362465337536990627⟩, ⟨710367279079293465, 710816968121398415⟩, true⟩

def words05 : List Nat := [371284992513876047, 371284993745177115, 371284994955511668, 371284995147007243, 371284995375477438, 371284995604490176, 371284996078458435, 371284996079634989, 371284995628191539, 371284995085887790]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 36150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 36100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487502036189022, 362487520448253109⟩, ⟨(-91739247870148779), (-91289177522359257)⟩, true⟩

def words06 : List Nat := [371284994763602078, 371284994764933247, 371284995151254613, 371284995579265110, 371284995890337538, 371284995891519817, 371284995756566289, 371284995997865977, 371284996554927984, 371284996625922448]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 36160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 36100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362471857929121786, 362471876351907560⟩, ⟨474312506026924886, 474762964231175174⟩, true⟩

def words07 : List Nat := [371284996699374899, 371284996773201405, 371284997472160273, 371284997791460888, 371284998334072943, 371284998877147904, 371284999427927097, 371284999429103997, 371284998962026292, 371284998600780727]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 36170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 36100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474444235180398, 362474462668451231⟩, ⟨380692082082029191, 381142919690677837⟩, true⟩

def words08 : List Nat := [371284998501611057, 371284998502788172, 371284997857645433, 371284997067494956, 371284996276927730, 371284995719025375, 371284994812838842, 371284994670135828, 371284994527062377, 371284994387702148]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 36180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 36100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362500845275615888, 362500863719534792⟩, ⟨(-574862732821061710), (-574411509806133808)⟩, true⟩

def words09 : List Nat := [371284994569367479, 371284995042644113, 371284995993555091, 371284995994732708, 371284995928850513, 371284995774069429, 371284995778702820, 371284995780011885, 371284995996934819, 371284996436592163]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 36190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 36100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 36100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk361
