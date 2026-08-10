import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk404A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579364853945972, 360579374915539562⟩, ⟨131648680208535743, 131923410798364451⟩, true⟩

def state01 : KState := ⟨⟨360537689266894448, 360537699333708365⟩, ⟨1815328720060953840, 1815603661577766406⟩, true⟩

def words00 : List Nat := [360582640266167028, 360582639823388921, 360582638770610755, 360582637810745678, 360582636850769777, 360582635734673069, 360582634203793713, 360582632366621152, 360582630529435938, 360582628897221797]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360495103141156116, 360495113213136536⟩, ⟨3536413446541219859, 3536688596862259863⟩, true⟩

def words01 : List Nat := [360582627785858043, 360582626453084455, 360582625120318100, 360582623414448736, 360582621667823374, 360582619622921270, 360582617577962098, 360582615710753296, 360582613858227214, 360582611694008933]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595587443155723, 360595597520309402⟩, ⟨(-525728864614869889), (-525453505165812757)⟩, true⟩

def words02 : List Nat := [360582609529773479, 360582607831093062, 360582606438168675, 360582605656011138, 360582604873861985, 360582603455470534, 360582602205061849, 360582601565383143, 360582600925570128, 360582601217839372]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574071972318329, 360574082054695250⟩, ⟨344387581118298179, 344663151769369355⟩, true⟩

def words03 : List Nat := [360582601233662631, 360582601249555596, 360582601875691107, 360582602888911320, 360582603745883355, 360582604602906061, 360582605151912749, 360582605152461011, 360582605092517584, 360582604882384899]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360559668395193948, 360559678482735404⟩, ⟨926905668229483917, 927181447759667025⟩, true⟩

def words04 : List Nat := [360582604812613032, 360582604813161438, 360582604525672871, 360582603752777561, 360582602979831114, 360582602051279867, 360582601600341447, 360582601242383433, 360582600884383290, 360582600150170749]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk404A
