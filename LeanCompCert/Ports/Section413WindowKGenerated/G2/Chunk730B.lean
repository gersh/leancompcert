import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk730A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk730B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk730A

def state06 : KState := ⟨⟨360567229464139519, 360567263983762363⟩, ⟨1105910462232181503, 1107613925671060575⟩, true⟩

def words05 : List Nat := [360582423645942743, 360582424028488103, 360582424316463853, 360582424417536504, 360582424429901151, 360582424442538615, 360582424575768550, 360582424576806687, 360582424523145439, 360582424316717073]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 73050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 73000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360622632548204110, 360622667077623539⟩, ⟨(-2942081038181289334), (-2940376858955714958)⟩, true⟩

def words06 : List Nat := [360582424110054120, 360582424228708514, 360582424554526112, 360582424880533505, 360582425046416769, 360582425296901623, 360582425660499762, 360582426024391887, 360582426528321679, 360582427080101188]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 73060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 73000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360601294268217964, 360601328807551875⟩, ⟨(-1382849618983314826), (-1381144715259958476)⟩, true⟩

def words07 : List Nat := [360582427509918033, 360582427939826193, 360582428218956137, 360582428612490976, 360582428904378914, 360582429196426526, 360582429394937604, 360582429467583064, 360582429727034371, 360582429986856210]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 73070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 73000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585613904799322, 360585648453907824⟩, ⟨(-236860001376698459), (-235154383276539779)⟩, true⟩

def words08 : List Nat := [360582430396910475, 360582430620278276, 360582430710353185, 360582430800543328, 360582430813423301, 360582430946255592, 360582431037581111, 360582431129088088, 360582431130023116, 360582431171571059]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 73080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 73000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360618874363824435, 360618908922740892⟩, ⟨(-2668022198320365669), (-2666315863309170453)⟩, true⟩

def words09 : List Nat := [360582431403385354, 360582431635497992, 360582431949695613, 360582432333729000, 360582432533829074, 360582432733997873, 360582433067634290, 360582433512626627, 360582434012450222, 360582434512496037]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 73090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 73000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 73000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk730B
