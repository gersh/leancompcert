import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk670

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362466579917609957, 362466646310148362⟩, ⟨1260678371933729677, 1263682739966079595⟩, true⟩

def state01 : KState := ⟨⟨362476938465244024, 362477004878242329⟩, ⟨566635952937712174, 569641691889675028⟩, true⟩

def words00 : List Nat := [371285506966624925, 371285506802116455, 371285506552431302, 371285506526169396, 371285506499191135, 371285506436721964, 371285506076837371, 371285505892355179, 371285505721896669, 371285505724263665]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 67000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 67000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480184982671049, 362480251416505041⟩, ⟨349067367610642323, 352074502869552109⟩, true⟩

def words01 : List Nat := [371285505599145581, 371285505429604531, 371285505259145899, 371285505252317823, 371285505162420858, 371285505115021387, 371285505066831394, 371285505010071002, 371285504767267859, 371285504691689607]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 67010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 67000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476819626717861, 362476886080905402⟩, ⟨574677272414950957, 577685771874617421⟩, true⟩

def words02 : List Nat := [371285504758820790, 371285504761113776, 371285504728753721, 371285504658264563, 371285504586900971, 371285504525254283, 371285504364470599, 371285504380141975, 371285504395289446, 371285504397657224]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 67020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 67000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362494618605877012, 362494685080801437⟩, ⟨(-618443147582285563), (-615433258029602193)⟩, true⟩

def words03 : List Nat := [371285504283909010, 371285504300014744, 371285504537088294, 371285504583263277, 371285504585191745, 371285504587810629, 371285504773762743, 371285504849318247, 371285504987834149, 371285505127369514]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 67030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 67000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486998742174610, 362487065237748868⟩, ⟨(-107628913113497026), (-104617639091905598)⟩, true⟩

def words04 : List Nat := [371285505265423023, 371285505267710789, 371285505171382370, 371285505236251204, 371285505280606783, 371285505282934672, 371285505142282285, 371285505002694474, 371285504942209485, 371285504968116918]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 67040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 67000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362480950814570722, 362481017330758493⟩, ⟨297968515289202234, 300981171552284964⟩, true⟩

def words05 : List Nat := [371285505155503675, 371285505343791489, 371285505498340692, 371285505500639851, 371285505450844593, 371285505461931912, 371285505693875584, 371285505696163915, 371285505632070132, 371285505567733625]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 67050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 67000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483218402652291, 362483284939306271⟩, ⟨145963888722476132, 148977917552975312⟩, true⟩

def words06 : List Nat := [371285505657500127, 371285505703872569, 371285505957430446, 371285506211932433, 371285506407122745, 371285506409411400, 371285506308286485, 371285506201108546, 371285506167251766, 371285506169626131]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 67060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 67000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497702720350863, 362497769277882816⟩, ⟨(-825565066837157597), (-822549637618304651)⟩, true⟩

def words07 : List Nat := [371285506138219899, 371285506110228368, 371285506272740454, 371285506386948986, 371285506566438624, 371285506746777786, 371285506908683972, 371285506910988669, 371285507056204457, 371285507241872347]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 67070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 67000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483159484611978, 362483226062560365⟩, ⟨150075300915369060, 153092099774928342⟩, true⟩

def words08 : List Nat := [371285507488483115, 371285507508037001, 371285507509748814, 371285507509467192, 371285507573555422, 371285507576101659, 371285507686145520, 371285507842128664, 371285507951676059, 371285507954046055]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 67080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 67000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496309788332956, 362496376386934370⟩, ⟨(-732249059662088768), (-729230875085691342)⟩, true⟩

def words09 : List Nat := [371285508048269946, 371285508177661088, 371285508445888837, 371285508448178538, 371285508420781939, 371285508339384902, 371285508375747354, 371285508398557065, 371285508562081661, 371285508726615065]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 67090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 67000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 67000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk670
