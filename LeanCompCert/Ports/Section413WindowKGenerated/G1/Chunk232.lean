import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk232

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362440012186674844, 362440019485186126⟩, ⟨1026665404958037101, 1026779898978893357⟩, true⟩

def state01 : KState := ⟨⟨362504490724979155, 362504498030004735⟩, ⟨(-469467712451846929), (-469353067265394775)⟩, true⟩

def words00 : List Nat := [371284275332367498, 371284275284764231, 371284275214958466, 371284276109976910, 371284276619494980, 371284276620223750, 371284275029949986, 371284274737663123, 371284276009975449, 371284276881960041]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 23200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 23200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362522796967395741, 362522804279064948⟩, ⟨(-894364941782399593), (-894250142364244869)⟩, true⟩

def words01 : List Nat := [371284277742349940, 371284278602912490, 371284281073340043, 371284282773500240, 371284285033110434, 371284287292813229, 371284289507640993, 371284290554312507, 371284292213461221, 371284293872865205]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 23210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 23200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362516834718224948, 362516842036383570⟩, ⟨(-755883306192034859), (-755768356055517679)⟩, true⟩

def words02 : List Nat := [371284296470608955, 371284297196381894, 371284297919722006, 371284298643251139, 371284299904361594, 371284300548428727, 371284303047013139, 371284305545671117, 371284307883408436, 371284309284627059]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 23220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 23200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362534877954131808, 362534885278903316⟩, ⟨(-1175131964436540845), (-1175016860649992149)⟩, true⟩

def words03 : List Nat := [371284311908040296, 371284314531617646, 371284317900743173, 371284318802339219, 371284319406179778, 371284320010188346, 371284321959914879, 371284322996029473, 371284325172184061, 371284327348493696]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 23230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 23200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362471459317114424, 362471466648463357⟩, ⟨298877135820246641, 298992392499626675⟩, true⟩

def words04 : List Nat := [371284329379849747, 371284329380579436, 371284329450313182, 371284329955446937, 371284331019229750, 371284331019959778, 371284329913658705, 371284328289466411, 371284326665109066, 371284326536312804]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 23240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 23200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362482782463844553, 362482789801761235⟩, ⟨35778547092456119, 35893956505234725⟩, true⟩

def words05 : List Nat := [371284327280903738, 371284328578761765, 371284329707072146, 371284329828652858, 371284330509237254, 371284331190140713, 371284333093160969, 371284333093891835, 371284333029656116, 371284332964121736]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 23250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 23200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362503870001639162, 362503877346100436⟩, ⟨(-454844070352669140), (-454728508679028086)⟩, true⟩

def words06 : List Nat := [371284333578670396, 371284333579474634, 371284334581281276, 371284335825474863, 371284336506803559, 371284336507534024, 371284334728669660, 371284334517163845, 371284335939725111, 371284336780216760]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 23260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 23200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497342241285070, 362497349592406475⟩, ⟨(-302913784102519726), (-302798067414322440)⟩, true⟩

def words07 : List Nat := [371284337619104533, 371284338458172141, 371284340154722806, 371284340939799688, 371284341802860530, 371284342666114888, 371284343528207309, 371284343528938201, 371284342801655712, 371284343361255996]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 23270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 23200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475157743089219, 362475165100725284⟩, ⟨213818221693560022, 213934090077229780⟩, true⟩

def words08 : List Nat := [371284345443774292, 371284346007377261, 371284346628648793, 371284347250098416, 371284348430741952, 371284348690146362, 371284349491660611, 371284350293405086, 371284350762915419, 371284350763674071]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 23280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 23200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362568338373005745, 362568345737249565⟩, ⟨(-1956772381270075559), (-1956656358958774807)⟩, true⟩

def words09 : List Nat := [371284351818873055, 371284353268711305, 371284356561331874, 371284357968918443, 371284359081534572, 371284360194309836, 371284363149673351, 371284365463867000, 371284369068668263, 371284372673477248]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 23290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 23200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 23200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk232
