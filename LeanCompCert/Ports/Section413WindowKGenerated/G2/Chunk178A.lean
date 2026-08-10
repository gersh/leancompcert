import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk178A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360511819303283279, 360511821123059971⟩, ⟨1282015985818443288, 1282037912051932408⟩, true⟩

def state01 : KState := ⟨⟨360595963196403134, 360595965018315181⟩, ⟨(-216298641529985920), (-216276677276671086)⟩, true⟩

def words00 : List Nat := [360583841678947868, 360583837531783343, 360583835574644959, 360583834936262005, 360583834297932941, 360583830964719800, 360583826114906733, 360583824406217845, 360583822697652002, 360583822147208749]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 17800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 17800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360571295267622896, 360571297091687339⟩, ⟨223140310414725061, 223162313012739825⟩, true⟩

def words01 : List Nat := [360583822147411830, 360583821212063904, 360583821347119631, 360583823986306348, 360583824454599892, 360583824922875207, 360583824923076565, 360583823818955188, 360583820931877589, 360583820229342375]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 17810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 17800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360617823221726919, 360617825047922829⟩, ⟨(-606111672296369157), (-606089631704888935)⟩, true⟩

def words02 : List Nat := [360583820878457455, 360583823646143847, 360583824409801008, 360583825173396430, 360583825173586407, 360583824298897134, 360583827776537444, 360583831253830909, 360583832359427099, 360583834266042683]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 17820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 17800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360704041519590609, 360704043347922250⟩, ⟨(-2144194538884019071), (-2144172460201799093)⟩, true⟩

def words03 : List Nat := [360583836651589245, 360583839036933045, 360583842445235658, 360583844243362501, 360583844243571278, 360583843106475755, 360583843961059957, 360583847570824344, 360583854308438993, 360583861045349424]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 17830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 17800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360624987961258505, 360624989791750438⟩, ⟨(-733890883030733256), (-733868765798711246)⟩, true⟩

def words04 : List Nat := [360583865838206961, 360583870225370926, 360583874511732303, 360583878797676216, 360583881623973727, 360583881624200342, 360583881337386080, 360583879497589546, 360583877657956435, 360583878998752920]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 17840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 17800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk178A
