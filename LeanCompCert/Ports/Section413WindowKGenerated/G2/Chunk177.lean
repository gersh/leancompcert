import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk177

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360517821360065615, 360517823158543683⟩, ⟨1173791171247875456, 1173812719430001500⟩, true⟩

def state01 : KState := ⟨⟨360581997358223073, 360581999158819152⟩, ⟨37173593679378385, 37195179360753169⟩, true⟩

def words00 : List Nat := [360584136515000890, 360584134577787698, 360584130739844893, 360584124478107062, 360584118217039970, 360584111138977063, 360584106217384222, 360584104472285320, 360584102727358465, 360584099394807902]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 17700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 17700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360629091912186967, 360629093714901786⟩, ⟨(-796887494267428286), (-796865871052469288)⟩, true⟩

def words01 : List Nat := [360584101444232712, 360584103612064498, 360584108953062980, 360584113334382561, 360584114984404351, 360584116634257786, 360584118181185775, 360584121319257782, 360584123857386282, 360584126395278037]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 17710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 17700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360558493948060601, 360558495752916874⟩, ⟨453853216055134538, 453874877227245064⟩, true⟩

def words02 : List Nat := [360584126528295391, 360584126528520296, 360584123501783821, 360584122242110755, 360584120982516583, 360584118870385478, 360584113599458669, 360584106346999690, 360584099095315880, 360584095012771767]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 17720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 17700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360453540141964968, 360453541948942896⟩, ⟨2314964000626278554, 2314985699425997150⟩, true⟩

def words03 : List Nat := [360584093569200097, 360584090567733146, 360584087566577700, 360584082475928494, 360584074228938968, 360584065166135170, 360584056104287703, 360584050209507751, 360584044553108587, 360584037196937598]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 17730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 17700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588515172951005, 360588516982053361⟩, ⟨(-80320203356397116), (-80298466858963498)⟩, true⟩

def words04 : List Nat := [360584029841545197, 360584024780022243, 360584021304087218, 360584018301595817, 360584015299429541, 360584009393893442, 360584002163605743, 360583998096311214, 360583994029406323, 360583993379616374]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 17740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 17700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk177
