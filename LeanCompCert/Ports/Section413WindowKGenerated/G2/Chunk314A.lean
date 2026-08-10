import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk314A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk314A
