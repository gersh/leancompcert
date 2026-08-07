import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk394

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479223745865767, 362479245747017978⟩, ⟨232881191616689659, 233466964451963825⟩, true⟩

def state01 : KState := ⟨⟨362505517849423434, 362505539862148119⟩, ⟨(-803260682706272380), (-802674453856801564)⟩, true⟩

def words00 : List Nat := [371285171416814172, 371285171459449788, 371285171657032435, 371285171855098330, 371285171902329507, 371285171903626576, 371285171636874431, 371285171787929535, 371285172582081745, 371285173100232492]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 39400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 39400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497511059255667, 362497533083722947⟩, ⟨(-487661073942570590), (-487074382257569292)⟩, true⟩

def words01 : List Nat := [371285173551402678, 371285174002964126, 371285174782114089, 371285175240100686, 371285175892995859, 371285176546369728, 371285177074630728, 371285177075921809, 371285177060249708, 371285177375286896]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 39410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 39400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488474607967643, 362488496643939712⟩, ⟨(-131345536438826336), (-130758391176497522)⟩, true⟩

def words02 : List Nat := [371285178266037483, 371285178464852241, 371285178582993186, 371285178701613577, 371285178965588669, 371285178967010971, 371285179420026004, 371285179931839218, 371285180426747781, 371285180512186105]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 39420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 39400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362514369256072051, 362514391303744827⟩, ⟨(-1152583871199697478), (-1151996264521018458)⟩, true⟩

def words03 : List Nat := [371285180780530813, 371285181049527205, 371285181855264219, 371285181856555731, 371285181805831392, 371285181554707404, 371285181631233565, 371285181730551105, 371285182472035574, 371285183214078718]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 39430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 39400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362513570429138080, 362513592488452923⟩, ⟨(-1121114212778261285), (-1120526146876563793)⟩, true⟩

def words04 : List Nat := [371285183955372376, 371285184225416692, 371285185137639607, 371285186050473688, 371285186922135853, 371285187245777359, 371285187571933611, 371285187898510473, 371285188782368047, 371285189503816880]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 39440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 39400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362480328712078706, 362480350783032477⟩, ⟨190603365092641255, 191191890209775365⟩, true⟩

def words05 : List Nat := [371285190866985829, 371285192230622930, 371285193593625545, 371285194101225986, 371285194721957969, 371285195343324919, 371285196109110930, 371285196110958794, 371285196111941690, 371285195990589745]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 39450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 39400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362505875103131876, 362505897185649130⟩, ⟨(-817509807913790119), (-816920826442153593)⟩, true⟩

def words06 : List Nat := [371285196388014816, 371285196587841251, 371285197140240066, 371285197693144712, 371285198143062218, 371285198144377034, 371285198526106088, 371285198990741546, 371285199924963676, 371285200450667951]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 39460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 39400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483656329874736, 362483678424198278⟩, ⟨59649317863397036, 60238765386885576⟩, true⟩

def words07 : List Nat := [371285200893591674, 371285201336945746, 371285202042303033, 371285202503448985, 371285203157421827, 371285203811843612, 371285204465557926, 371285204466850907, 371285204265800824, 371285204228792678]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 39470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 39400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362464916888976432, 362464938994807149⟩, ⟨799599520421113475, 800189422308834629⟩, true⟩

def words08 : List Nat := [371285204576340543, 371285204577636385, 371285204304990364, 371285203967146263, 371285203628836555, 371285203419180083, 371285202888381378, 371285202620718429, 371285202352614375, 371285202084761792]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 39480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 39400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362515905968800873, 362515928086302317⟩, ⟨(-1214266371620818420), (-1213676008797197418)⟩, true⟩

def words09 : List Nat := [371285201572536736, 371285201266846003, 371285201217378447, 371285201218701945, 371285201150670312, 371285200977474156, 371285201192697177, 371285201331183027, 371285202109953523, 371285202889249149]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 39490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 39400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 39400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk394
