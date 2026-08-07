import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk403

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360533216343394904, 360533226353237426⟩, ⟨1993151991790467795, 1993424634226333099⟩, true⟩

def state01 : KState := ⟨⟨360598842093527733, 360598852108523693⟩, ⟨(-651906828685132725), (-651633978539684339)⟩, true⟩

def words00 : List Nat := [360582689757421731, 360582689007946766, 360582688571176446, 360582688491359471, 360582688411500275, 360582687807199197, 360582687217250440, 360582686832249450, 360582686541633192, 360582686943220434]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360558591160043089, 360558601180254935⟩, ⟨970764984088090059, 971038044512182513⟩, true⟩

def words01 : List Nat := [360582687033357876, 360582687123545530, 360582687123997218, 360582687096180705, 360582687096641228, 360582686832815140, 360582686568942618, 360582685946488958, 360582685061768012, 360582684465089067]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360551887167665881, 360551897193023391⟩, ⟨1241044894982539231, 1241318162905372245⟩, true⟩

def words02 : List Nat := [360582683868242361, 360582683703073751, 360582682925616746, 360582681840461262, 360582680755269632, 360582679514113326, 360582678790830083, 360582678037112819, 360582677283377714, 360582676220122459]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575645388771429, 360575655419288975⟩, ⟨282843970053690194, 283117446106109180⟩, true⟩

def words03 : List Nat := [360582675457404403, 360582675062009290, 360582674689199270, 360582674946258900, 360582674946763033, 360582674680699309, 360582674414548091, 360582673981652720, 360582673873471575, 360582673700055116]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360564340942009456, 360564350977740992⟩, ⟨738718720657413347, 738992407067819459⟩, true⟩

def words04 : List Nat := [360582673526578257, 360582672815554155, 360582671829995746, 360582671457772582, 360582671085423009, 360582670556603571, 360582669416181478, 360582667966803256, 360582666517379125, 360582665535536973]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360532759774368948, 360532769815251135⟩, ⟨2013276299184702105, 2013550193450048215⟩, true⟩

def words05 : List Nat := [360582665241097487, 360582665400638509, 360582665401125935, 360582665253269249, 360582664493946571, 360582663313536633, 360582662133018122, 360582661565369657, 360582660797946236, 360582659562363377]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 40350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 40300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360572113758555329, 360572123804610663⟩, ⟨424883685107324550, 425157788185403848⟩, true⟩

def words06 : List Nat := [360582658326717983, 360582657703940106, 360582657859808325, 360582658172168061, 360582658172680895, 360582657913580918, 360582657043357284, 360582656524736537, 360582656005988584, 360582655332680651]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 40360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 40300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567558547432020, 360567568598696579⟩, ⟨608772903526227276, 609047216926492714⟩, true⟩

def words07 : List Nat := [360582655072299668, 360582654504848886, 360582653937321690, 360582653930426671, 360582653930887636, 360582653642250371, 360582653353558291, 360582652697250715, 360582651864545868, 360582651491636810]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 40370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 40300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360568963698571905, 360568973754995669⟩, ⟨551851939172251087, 552126460927231725⟩, true⟩

def words08 : List Nat := [360582651118567982, 360582650838092687, 360582650160926293, 360582649009382038, 360582647857805833, 360582646414336883, 360582645337281785, 360582644872165346, 360582644407011453, 360582643635186985]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 40380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 40300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579364853945972, 360579374915539562⟩, ⟨131648680208535743, 131923410798364451⟩, true⟩

def words09 : List Nat := [360582643297193204, 360582643097591219, 360582643064550042, 360582643065098867, 360582642970156201, 360582642354139953, 360582641738057534, 360582640929204645, 360582640426761786, 360582640346499918]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 40390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 40300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 40300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk403
