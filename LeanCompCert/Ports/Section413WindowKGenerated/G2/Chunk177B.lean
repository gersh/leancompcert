import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk177A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk177B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk177A

def state06 : KState := ⟨⟨360532867076187447, 360532868887436633⟩, ⟨907857380809073768, 907879155423330268⟩, true⟩

def words05 : List Nat := [360583993379816981, 360583991493454874, 360583989607258551, 360583991828987965, 360583992680851667, 360583993532656465, 360583993532858931, 360583992756025330, 360583991087496627, 360583988209251010]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 17750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 17700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360536498836228855, 360536500649600288⟩, ⟨843304450991509274, 843326263307357404⟩, true⟩

def words06 : List Nat := [360583985611743203, 360583985611968645, 360583983816897086, 360583980192903836, 360583976569283977, 360583969924886725, 360583965781234642, 360583963886011604, 360583961990977213, 360583958514727320]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 17760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 17700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360527943287586240, 360527945103089066⟩, ⟨995140426442795036, 995162276644184948⟩, true⟩

def words07 : List Nat := [360583955844387653, 360583954056530801, 360583952268812546, 360583950376555993, 360583945343772685, 360583937590622121, 360583929838299433, 360583923696661194, 360583919132698339, 360583915984790089]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 17770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 17700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360521352213804846, 360521354031455936⟩, ⟨1112001627769881017, 1112023516178132895⟩, true⟩

def words08 : List Nat := [360583912837199530, 360583908112721865, 360583902424018112, 360583899884716408, 360583897345636956, 360583893996712363, 360583887512149014, 360583878084751159, 360583868658370135, 360583862379751503]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 17780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 17700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360511819303283279, 360511821123059971⟩, ⟨1282015985818443288, 1282037912051932408⟩, true⟩

def words09 : List Nat := [360583858866452752, 360583858499868182, 360583858133302063, 360583856195097742, 360583855639959656, 360583854276868687, 360583852913866064, 360583851540979217, 360583849771179958, 360583845724860642]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 17790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 17700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 17700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk177B
