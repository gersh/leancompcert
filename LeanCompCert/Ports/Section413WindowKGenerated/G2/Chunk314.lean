import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk314

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360647224604920947, 360647230558179642⟩, ⟨(-2021951026479207090), (-2021824616250033580)⟩, true⟩

def state01 : KState := ⟨⟨360616878516726465, 360616884473971269⟩, ⟨(-1069027845062601642), (-1068901309650040470)⟩, true⟩

def words00 : List Nat := [360582844828340580, 360582846403597345, 360582848574958404, 360582850746303112, 360582852235038003, 360582853170102154, 360582853419309298, 360582853668547009, 360582853868280756, 360582854952158846]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 31400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 31400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360573825848908727, 360573831810086733⟩, ⟨283559809546118838, 283686468520212514⟩, true⟩

def words01 : List Nat := [360582856751543708, 360582858550893856, 360582859703112342, 360582860122553700, 360582860122903545, 360582860078769525, 360582860719090716, 360582860946696001, 360582860947071798, 360582860660135117]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 31410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 31400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360600466910516939, 360600472875644942⟩, ⟨(-553751305896852097), (-553624522794313959)⟩, true⟩

def words02 : List Nat := [360582860386132466, 360582860911022868, 360582861246320887, 360582861581671604, 360582861582057347, 360582861042368053, 360582860085596808, 360582859286326797, 360582858486980812, 360582858910998755]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 31420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 31400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595259977366018, 360595265946472787⟩, ⟨(-390141398995811202), (-390014490820744592)⟩, true⟩

def words03 : List Nat := [360582858967134779, 360582859023312868, 360582859164927420, 360582859974969635, 360582860529592055, 360582861084247729, 360582861084630082, 360582860862412526, 360582860904939727, 360582861299965973]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 31430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 31400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360560159396689082, 360560165369734600⟩, ⟨713523693024754971, 713650725053810215⟩, true⟩

def words04 : List Nat := [360582862154342837, 360582862298077258, 360582862298449927, 360582861808865420, 360582861319237506, 360582860317934065, 360582859821592408, 360582859130098156, 360582858438604768, 360582856966715644]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 31440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 31400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360594288122822338, 360594294099821304⟩, ⟨(-360202174450081023), (-360075018065787117)⟩, true⟩

def words05 : List Nat := [360582856245569384, 360582855497796154, 360582854749948248, 360582854707455044, 360582853656761254, 360582851734080756, 360582849811442627, 360582848635211778, 360582848612477371, 360582848976714417]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 31450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 31400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360547230883052164, 360547236864031468⟩, ⟨1120156077726948707, 1120283359352633417⟩, true⟩

def words06 : List Nat := [360582848977087249, 360582848837816259, 360582847690683901, 360582847263949353, 360582846837132158, 360582845564173316, 360582843283588261, 360582840293043013, 360582837302607907, 360582835318411914]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 31460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 31400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360466968901413886, 360466974886339331⟩, ⟨3646479255142589661, 3646606660973456877⟩, true⟩

def words07 : List Nat := [360582834187601806, 360582833214392161, 360582832241196788, 360582830618545620, 360582827988571007, 360582825091604378, 360582822194699218, 360582820303462991, 360582817405076722, 360582813725633279]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 31470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 31400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575359712551629, 360575365701431781⟩, ⟨233797922969163851, 233925453313470285⟩, true⟩

def words08 : List Nat := [360582810046329112, 360582807372644466, 360582805481304342, 360582804031205227, 360582802581164498, 360582800270062145, 360582798402089297, 360582796687929055, 360582794973755107, 360582794264572889]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 31480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 31400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360515455647732380, 360515461640610263⟩, ⟨2120486132336070588, 2120613788587971450⟩, true⟩

def words09 : List Nat := [360582794029054757, 360582793281666680, 360582792534254178, 360582791244108979, 360582790571061098, 360582789643661969, 360582788716275760, 360582787286330229, 360582784850018004, 360582782713263850]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 31490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 31400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 31400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk314
