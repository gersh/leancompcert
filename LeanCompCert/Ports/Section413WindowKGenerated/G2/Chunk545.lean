import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk545

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584158833799346, 360584177598495674⟩, ⟨(-132738413369221548), (-132047439605274134)⟩, true⟩

def state01 : KState := ⟨⟨360569212097820047, 360569230869737024⟩, ⟨681930826648986580, 682622193974052306⟩, true⟩

def words00 : List Nat := [360581754754826473, 360581754585096412, 360581754898048667, 360581755223041147, 360581755326867939, 360581755327625299, 360581755095785057, 360581754695751592, 360581754295601477, 360581753749831944]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360535927392170338, 360535946171218472⟩, ⟨2496507843906821578, 2497199599985958480⟩, true⟩

def words01 : List Nat := [360581753520714480, 360581753400864715, 360581753280943668, 360581752993118303, 360581752470539911, 360581751863511659, 360581751256263343, 360581750985006328, 360581750378140600, 360581749538789748]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360566397333230603, 360566416119440209⟩, ⟨835123821751824510, 835815968309556380⟩, true⟩

def words02 : List Nat := [360581748699297244, 360581748195865122, 360581747911383843, 360581747618780316, 360581747326129040, 360581746746109601, 360581745909028092, 360581745123007085, 360581744336793201, 360581743755022633]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575166014922767, 360575184808353226⟩, ⟨356850650806474924, 357543191152008442⟩, true⟩

def words03 : List Nat := [360581743474622914, 360581743005991396, 360581742537232885, 360581742225086814, 360581742124693211, 360581741837096332, 360581741549437329, 360581740996901307, 360581740541746633, 360581740422419087]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577925926776752, 360577944727340745⟩, ⟨206304250931771919, 206997180376677751⟩, true⟩

def words04 : List Nat := [360581740518181947, 360581740518939788, 360581740399687199, 360581740112492162, 360581739825170912, 360581739453504614, 360581739382433682, 360581739515080662, 360581739515768723, 360581739359428311]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360595927011980402, 360595945819706873⟩, ⟨(-775896570436633473), (-775203250242533097)⟩, true⟩

def words05 : List Nat := [360581739290490542, 360581739213601328, 360581739170397202, 360581739171155146, 360581738870630931, 360581738284470813, 360581737698186040, 360581737362044938, 360581737548200858, 360581737809402031]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 54550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 54500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574263284979332, 360574282099916610⟩, ⟨406011990512773321, 406705704164092925⟩, true⟩

def words06 : List Nat := [360581737853834049, 360581737854592122, 360581737607883866, 360581737652695479, 360581737653340950, 360581737467395131, 360581736946354229, 360581736210908784, 360581735475343570, 360581735017346775]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 54560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 54500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360540800588601890, 360540819410689167⟩, ⟨2232256508032919124, 2232950611895382704⟩, true⟩

def words07 : List Nat := [360581734881391332, 360581734705579827, 360581734529678887, 360581734185969660, 360581733744993743, 360581733104360862, 360581732463521374, 360581732157945668, 360581731676744891, 360581730927946320]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 54570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 54500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360590929554035113, 360590948383278759⟩, ⟨(-503963202677308307), (-503268708184531663)⟩, true⟩

def words08 : List Nat := [360581730179003422, 360581729765365914, 360581729787513571, 360581729966554383, 360581729967260146, 360581729858628453, 360581729771667930, 360581729537394401, 360581729318412490, 360581729488072873]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 54580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 54500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360558472951369322, 360558491787846421⟩, ⟨1267973740849897930, 1268668630251682594⟩, true⟩

def words09 : List Nat := [360581729488749036, 360581729463908766, 360581729438939036, 360581729239032847, 360581729216405983, 360581729055308189, 360581728894133530, 360581728565315488, 360581727901729911, 360581727477045170]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 54590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 54500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 54500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk545
