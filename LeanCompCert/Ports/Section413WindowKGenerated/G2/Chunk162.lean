import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk162

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360675066837341278, 360675068331712344⟩, ⟨(-1504381891406756298), (-1504365501542808584)⟩, true⟩

def state01 : KState := ⟨⟨360595959524442973, 360595961020732704⟩, ⟨(-222692336139769551), (-222675915183469193)⟩, true⟩

def words00 : List Nat := [360582218920898071, 360582222069478494, 360582222363881501, 360582222658269223, 360582222658442906, 360582220593245313, 360582222387272185, 360582224181116245, 360582224181299728, 360582224920850929]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 16200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 16200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360662233888483703, 360662235386703761⟩, ⟨(-1297551952308952768), (-1297535500052785410)⟩, true⟩

def words01 : List Nat := [360582224943717691, 360582224966643844, 360582227154018955, 360582229425235092, 360582229425423593, 360582228083092488, 360582229195182393, 360582234430651802, 360582239363061413, 360582244294905920]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 16210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 16200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360693374877680246, 360693376377844466⟩, ⟨(-1803476348153009727), (-1803459864352780221)⟩, true⟩

def words02 : List Nat := [360582247299081152, 360582247299285403, 360582249565717086, 360582252595653683, 360582252685398753, 360582254427068404, 360582254427252274, 360582254177855086, 360582257470381341, 360582264316705117]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 16220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 16200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360569249200678027, 360569250702770164⟩, ⟨211961138657523889, 211977653757501699⟩, true⟩

def words03 : List Nat := [360582274953123209, 360582285588269769, 360582293307133782, 360582297260909235, 360582298885529550, 360582300510006696, 360582303197223348, 360582304317358720, 360582304317540929, 360582303513962129]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 16230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 16200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360626039870366143, 360626041374387422⟩, ⟨(-710556150694351010), (-710539604255498436)⟩, true⟩

def words04 : List Nat := [360582304554901860, 360582308303003176, 360582314101591791, 360582319899505548, 360582322566521672, 360582322566726199, 360582321475452476, 360582318342557742, 360582315860066590, 360582318550914682]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 16240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 16200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360690753222167427, 360690754728136232⟩, ⟨(-1762493563566504056), (-1762476985470859456)⟩, true⟩

def words05 : List Nat := [360582319322107105, 360582320093227448, 360582324644894597, 360582332307844804, 360582338973188414, 360582345637745312, 360582350384920157, 360582354642524996, 360582361309362659, 360582367975447538]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 16250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 16200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360620940680176708, 360620942188076503⟩, ⟨(-627275326125251225), (-627258716622179879)⟩, true⟩

def words06 : List Nat := [360582373081407930, 360582375933813958, 360582376348121676, 360582376762398660, 360582376762570144, 360582377500109764, 360582382589561941, 360582387678430974, 360582389101409641, 360582391471057133]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 16260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 16200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360733554939604716, 360733556449438221⟩, ⟨(-2460149664606652743), (-2460133023632590619)⟩, true⟩

def words07 : List Nat := [360582396229225753, 360582400986871164, 360582409514255167, 360582415763384992, 360582418655289439, 360582421546851997, 360582426501920413, 360582433344222280, 360582442627134267, 360582451908953448]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 16270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 16200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360675820084365664, 360675821596154817⟩, ⟨(-1520079209984559204), (-1520062537163068268)⟩, true⟩

def words08 : List Nat := [360582458957473748, 360582466144179298, 360582474881079485, 360582483616966298, 360582491363512905, 360582497930937838, 360582502169941984, 360582506408447964, 360582508978536639, 360582514706635263]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 16280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 16200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360551217450711317, 360551218964431134⟩, ⟨510372522503107481, 510389226785010863⟩, true⟩

def words09 : List Nat := [360582520937731195, 360582527168100218, 360582531493084295, 360582532087294744, 360582532087466622, 360582531696987269, 360582533140261523, 360582533140466928, 360582533107833864, 360582531186933282]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 16290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 16200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 16200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk162
