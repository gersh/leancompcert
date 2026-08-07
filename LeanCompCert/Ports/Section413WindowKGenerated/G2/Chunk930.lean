import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk930

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589409669684652, 360589466666466259⟩, ⟨(-695962572152968758), (-692383193696036396)⟩, true⟩

def state01 : KState := ⟨⟨360594684169710657, 360594741179186594⟩, ⟨(-1186472888514782164), (-1182892329423539216)⟩, true⟩

def words00 : List Nat := [360582021962622934, 360582022216409458, 360582022399865881, 360582022583464223, 360582022670641579, 360582022816571434, 360582023001208841, 360582023186097296, 360582023272950199, 360582023411079343]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360615465105043140, 360615522127220477⟩, ⟨(-3119446761974358100), (-3115865021464814830)⟩, true⟩

def words01 : List Nat := [360582023645216119, 360582023879745347, 360582024192186695, 360582024389585255, 360582024485891334, 360582024582313726, 360582024774344420, 360582025043266590, 360582025404460946, 360582025765952970]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591578185967032, 360591635220987859⟩, ⟨(-897482062477802901), (-893899127205452813)⟩, true⟩

def words02 : List Nat := [360582026059410268, 360582026237725632, 360582026385204008, 360582026533076701, 360582026638155317, 360582026651764313, 360582026652971789, 360582026579749830, 360582026506265491, 360582026605287658]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360571121059952681, 360571178107635754⟩, ⟨1005779525443481468, 1009363638750202948⟩, true⟩

def words03 : List Nat := [360582026780131739, 360582026955230531, 360582027072850691, 360582027098296586, 360582027099424905, 360582027062840340, 360582027025880150, 360582026986567610, 360582026929195128, 360582026813985176]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360570224026464035, 360570281086856770⟩, ⟨1089221418739033852, 1092806714616957200⟩, true⟩

def words04 : List Nat := [360582026698480417, 360582026561111078, 360582026481003709, 360582026408518936, 360582026335907545, 360582026165128555, 360582025878884253, 360582025708463595, 360582025537658592, 360582025382553890]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360586474426376444, 360586531499628592⟩, ⟨(-423018152098206978), (-419431659592044442)⟩, true⟩

def words05 : List Nat := [360582025257572767, 360582025042989801, 360582024828152843, 360582024729132669, 360582024703197051, 360582024623334641, 360582024543326982, 360582024405479251, 360582024388034754, 360582024438028222]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360586996070904676, 360587053156823694⟩, ⟨(-471573315033096979), (-467985643684346809)⟩, true⟩

def words06 : List Nat := [360582024549805351, 360582024660886508, 360582024703830022, 360582024746919480, 360582024748066234, 360582024730913591, 360582024785948719, 360582024841235990, 360582024842448404, 360582024891911054]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360594353352116658, 360594410450768118⟩, ⟨(-1156375104171776142), (-1152786247751594254)⟩, true⟩

def words07 : List Nat := [360582024964651582, 360582025037804601, 360582025201682091, 360582025275560038, 360582025276807223, 360582025240177347, 360582025280664229, 360582025417825305, 360582025551991053, 360582025686447241]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360609745184041315, 360609802295511158⟩, ⟨(-2589222817013511558), (-2585632767394687278)⟩, true⟩

def words08 : List Nat := [360582025732225504, 360582025760219831, 360582025903279389, 360582026046731518, 360582026160901550, 360582026302591132, 360582026386862869, 360582026471268612, 360582026670733036, 360582026970642002]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590686660316756, 360590743784501004⟩, ⟨(-814931519760085283), (-811340286497447597)⟩, true⟩

def words09 : List Nat := [360582027361783920, 360582027753180079, 360582028041326587, 360582028243776730, 360582028396277300, 360582028549146845, 360582028816904329, 360582028969832005, 360582029064639436, 360582029159668860]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk930
