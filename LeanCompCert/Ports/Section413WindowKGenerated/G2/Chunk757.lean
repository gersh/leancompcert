import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk757

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575494263248518, 360575531426815655⟩, ⟨503154748026154994, 505054890046717104⟩, true⟩

def state01 : KState := ⟨⟨360605386440313601, 360605423614055413⟩, ⟨(-1759866619924419420), (-1757965707632286168)⟩, true⟩

def words00 : List Nat := [360582203134669606, 360582203099533605, 360582203331212159, 360582203563091079, 360582203627160112, 360582203628238528, 360582203581043412, 360582203645351707, 360582203883608061, 360582204191413627]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 75700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 75700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360586217876283136, 360586255060309811⟩, ⟨(-308493724063997486), (-306592033053599094)⟩, true⟩

def words01 : List Nat := [360582204411751903, 360582204632225938, 360582204879604773, 360582205214750670, 360582205466570246, 360582205718558627, 360582205869754986, 360582205981565314, 360582206035927737, 360582206090630943]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 75710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 75700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585490444548349, 360585527638731091⟩, ⟨(-253429022037693439), (-251526561958344315)⟩, true⟩

def words02 : List Nat := [360582206319202115, 360582206373806112, 360582206374767602, 360582206322704559, 360582206270465186, 360582206118056123, 360582206189518491, 360582206277457094, 360582206278418278, 360582206322995681]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 75720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 75700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592920879149963, 360592958083533859⟩, ⟨(-816177668312208272), (-814274435650744440)⟩, true⟩

def words03 : List Nat := [360582206541905639, 360582206761126327, 360582206933666661, 360582207032451690, 360582207033466573, 360582206943896547, 360582206882014749, 360582207022813318, 360582207165634327, 360582207308713739]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 75730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 75700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593947125417938, 360593984340066659⟩, ⟨(-894031429858049247), (-892127419687455081)⟩, true⟩

def words04 : List Nat := [360582207364395585, 360582207365474494, 360582207301769481, 360582207357746518, 360582207369369560, 360582207370455836, 360582207363004846, 360582207221252361, 360582207079296161, 360582207235874141]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 75740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 75700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360563406504660141, 360563443729467259⟩, ⟨1419643561994966671, 1421548341715381345⟩, true⟩

def words05 : List Nat := [360582207444101015, 360582207652527739, 360582207754448149, 360582207863626474, 360582207910570108, 360582207957798616, 360582207972171732, 360582207973250853, 360582207813696009, 360582207567135097]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 75750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 75700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360582041065534972, 360582078300550478⟩, ⟨7780027976280039, 9685581132296465⟩, true⟩

def words06 : List Nat := [360582207320351596, 360582207036607413, 360582206872096858, 360582206850734904, 360582206829283512, 360582206659761725, 360582206381702755, 360582206278019580, 360582206173995630, 360582206129257517]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 75760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 75700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360563830316620558, 360563867561919318⟩, ⟨1387763714717906449, 1389670047086806815⟩, true⟩

def words07 : List Nat := [360582206128541248, 360582206039905215, 360582206035344928, 360582206217531250, 360582206277211297, 360582206337049416, 360582206338016812, 360582206265657814, 360582206019182064, 360582205778428778]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 75770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 75700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587504682050019, 360587541937531041⟩, ⟨(-406409858950395267), (-404502754919106459)⟩, true⟩

def words08 : List Nat := [360582205537311978, 360582205470387008, 360582205408566171, 360582205259751513, 360582205110766230, 360582204871960235, 360582204808417470, 360582204864257960, 360582204865246765, 360582204855886531]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 75780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 75700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360612309071128776, 360612346336788258⟩, ⟨(-2286510920398138171), (-2284603044889677237)⟩, true⟩

def words09 : List Nat := [360582205003570526, 360582205151565504, 360582205473149856, 360582205621086542, 360582205622083213, 360582205621979114, 360582205794340411, 360582206055308403, 360582206453810513, 360582206852548081]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 75790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 75700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 75700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk757
