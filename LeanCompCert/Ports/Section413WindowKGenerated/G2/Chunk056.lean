import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk056

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360626100542070719, 360626100702805584⟩, ⟨(-277823035765586068), (-277822424825417670)⟩, true⟩

def state01 : KState := ⟨⟨360268174744179656, 360268174905522523⟩, ⟨1726653768356918966, 1726654382704903524⟩, true⟩

def words00 : List Nat := [360576498413123986, 360576491087961788, 360576452204496150, 360576421366105236, 360576390538701844, 360576340523425023, 360576258987395526, 360576152295448278, 360576045641532205, 360575956435416446]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 5600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 5600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360105644577548676, 360105644739494193⟩, ⟨2640041234591763575, 2640041852323722475⟩, true⟩

def words01 : List Nat := [360575901582228366, 360575863588724918, 360575825608752166, 360575771605420705, 360575719560387783, 360575659439444185, 360575599339888099, 360575554350050192, 360575486677908788, 360575403076206600]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 5610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 5600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360201113989289921, 360201114151841942⟩, ⟨2102757148720654736, 2102757769864158054⟩, true⟩

def words02 : List Nat := [360575319504237662, 360575217283272954, 360575131403699464, 360575076817330202, 360575022250364836, 360574940852784174, 360574848515447791, 360574764854778929, 360574681223815664, 360574605762830248]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 5620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 5600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360058899059304887, 360058899222467951⟩, ⟨2904061404507932737, 2904062029094717331⟩, true⟩

def words03 : List Nat := [360574539435128490, 360574457279464482, 360574375152957456, 360574309445323403, 360574260038877054, 360574184441764423, 360574108871466619, 360574017551769767, 360573895148817182, 360573803837555667]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 5630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 5600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360317568877855471, 360317569041625391⟩, ⟨1444422203296479475, 1444422831308956219⟩, true⟩

def words04 : List Nat := [360573712558647553, 360573652349504543, 360573608733375901, 360573539686140810, 360573470663358364, 360573393733028251, 360573332979871725, 360573303221585984, 360573273473830020, 360573219100264145]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 5640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 5600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360978746960079841, 360978747124458359⟩, ⟨(-2294939069515769294), (-2294938438061645154)⟩, true⟩

def words05 : List Nat := [360573173860525485, 360573159584661937, 360573161985018260, 360573175981261943, 360573175981321651, 360573163197837605, 360573168542491848, 360573209319415807, 360573280969257075, 360573352593799175]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 5650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 5600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360723540736395159, 360723540901390535⟩, ⟨(-851127619485119413), (-851126984536580597)⟩, true⟩

def words06 : List Nat := [360573399101983781, 360573435848127992, 360573471050513281, 360573506240488220, 360573518903308037, 360573518903372679, 360573500755335505, 360573467005705113, 360573433267969021, 360573456791967756]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 5660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 5600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360341572606093641, 360341572771698397⟩, ⟨1317050225118453883, 1317050863525268141⟩, true⟩

def words07 : List Nat := [360573500955275324, 360573545103025420, 360573569744505146, 360573569744569893, 360573563635863535, 360573547478698710, 360573531327207933, 360573513727425586, 360573488753939111, 360573447923727494]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 5670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 5600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360427085004843300, 360427085171060366⟩, ⟨830486840002376211, 830487481890192219⟩, true⟩

def words08 : List Nat := [360573407107876271, 360573353845325994, 360573316530405603, 360573309864913344, 360573303201759849, 360573269779425866, 360573205771908939, 360573140559170470, 360573075369338722, 360573040791779205]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 5680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 5600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360570848175899968, 360570848342737123⟩, ⟨11156399935456776, 11157045354585528⟩, true⟩

def words09 : List Nat := [360573015145093980, 360572965402760217, 360572915677889181, 360572897272106245, 360572897272160937, 360572877380933145, 360572857496681944, 360572821427308801, 360572806062500663, 360572805719115121]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 5690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 5600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 5600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk056
