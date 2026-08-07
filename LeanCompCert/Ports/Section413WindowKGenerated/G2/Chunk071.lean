import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk071

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360654669541508465, 360654669806275105⟩, ⟨(-491920398054764558), (-491919123145691678)⟩, true⟩

def state01 : KState := ⟨⟨360787192452085942, 360787192717642592⟩, ⟨(-1434770177627335470), (-1434768897105363470)⟩, true⟩

def words00 : List Nat := [360585395179797717, 360585394527858879, 360585393895829619, 360585403437328467, 360585403437399198, 360585402074892251, 360585402074966278, 360585393753368376, 360585396810781556, 360585425188869514]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 7100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 7100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360347053569621718, 360347053835961121⟩, ⟨1697479586915613424, 1697480873006979368⟩, true⟩

def words01 : List Nat := [360585458476807672, 360585491755402913, 360585515003726373, 360585518763600108, 360585518763669730, 360585517039409116, 360585516173476000, 360585516173559101, 360585497560135195, 360585464070934012]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 7110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 7100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360855718521522871, 360855718788647305⟩, ⟨(-1927192731788248238), (-1927191440103568116)⟩, true⟩

def words02 : List Nat := [360585430591120047, 360585416734668595, 360585414564883367, 360585416262758536, 360585416262835376, 360585401689642257, 360585393996323869, 360585399940593442, 360585425458953343, 360585463363026275]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 7120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 7100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360667272013833057, 360667272281750888⟩, ⟨(-582390430187797014), (-582389132842332426)⟩, true⟩

def words03 : List Nat := [360585491312121131, 360585519253388531, 360585546354560386, 360585587483936956, 360585623179099927, 360585658864273587, 360585681104183137, 360585693750581862, 360585705176214343, 360585716598675362]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 7130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 7100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360601643168231911, 360601643436934136⟩, ⟨(-114103840637766336), (-114102537687695846)⟩, true⟩

def words04 : List Nat := [360585737784581693, 360585739625246393, 360585739625320613, 360585731593268436, 360585723563450874, 360585710163641463, 360585706920119355, 360585702903050366, 360585698887096119, 360585687271686242]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 7140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 7100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360947547651691975, 360947547921180500⟩, ⟨(-2589208456442072886), (-2589207147865955458)⟩, true⟩

def words05 : List Nat := [360585708927459601, 360585730577202064, 360585760158393086, 360585792663823485, 360585808288344287, 360585823908504694, 360585845153026190, 360585876298192933, 360585926811057057, 360585977309832092]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 7150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 7100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360597180324978862, 360597180595264386⟩, ⟨(-80481672785445082), (-80480358498826250)⟩, true⟩

def words06 : List Nat := [360586010526583560, 360586024499844403, 360586032031504047, 360586039561085849, 360586041779085356, 360586041779168993, 360586024772927361, 360585998017000379, 360585971268520557, 360585957563818448]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 7160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 7100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360463287940753442, 360463288211827256⟩, ⟨880487491383448028, 880488811326104914⟩, true⟩

def words07 : List Nat := [360585969822974969, 360585982078729758, 360585984304359887, 360585984304443830, 360585981416225928, 360585962322206917, 360585943417109898, 360585943417193692, 360585936047278468, 360585918965493845]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 7170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 7100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360522713109420510, 360522713381286701⟩, ⟨454130663541431724, 454131989177260354⟩, true⟩

def words08 : List Nat := [360585901888448047, 360585904200965692, 360585915722053576, 360585927239949957, 360585927240027205, 360585922402005789, 360585898451555969, 360585893715858252, 360585888981455283, 360585874993133330]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 7180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 7100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360550259306877938, 360550259579544075⟩, ⟨256007668861308858, 256009000252706914⟩, true⟩

def words09 : List Nat := [360585866209783638, 360585843261885553, 360585820320352085, 360585827329275442, 360585832852215072, 360585838373634934, 360585838373709787, 360585834241715275, 360585821324169482, 360585816385134729]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 7190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 7100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 7100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk071
