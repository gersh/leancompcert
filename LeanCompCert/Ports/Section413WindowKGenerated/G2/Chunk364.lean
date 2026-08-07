import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk364

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360546330477545399, 360546338576286165⟩, ⟨1294675526544477518, 1294874810355207118⟩, true⟩

def state01 : KState := ⟨⟨360584887101475068, 360584895204832418⟩, ⟨(-108943289224255185), (-108743837346723661)⟩, true⟩

def words00 : List Nat := [360581911083216432, 360581910658945312, 360581911062409789, 360581911511298083, 360581911511753563, 360581911308851039, 360581910556795715, 360581909774059100, 360581908991222220, 360581908639306980]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 36400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 36400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360579225327160199, 360579233435177193⟩, ⟨97214271847755646, 97413893406259506⟩, true⟩

def words01 : List Nat := [360581908639743295, 360581908269991975, 360581907900169078, 360581908284232621, 360581908622165152, 360581908960159136, 360581908960595522, 360581908868665171, 360581908244289870, 360581908171404713]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 36410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 36400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360531953840641384, 360531961953277186⟩, ⟨1818850364461296108, 1819050154259713874⟩, true⟩

def words02 : List Nat := [360581908098371155, 360581907526983973, 360581906204004776, 360581904383072286, 360581902562160280, 360581900365893754, 360581898633946553, 360581897450697815, 360581896267452058, 360581894705246984]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 36420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 36400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360557061984748641, 360557070102008081⟩, ⟨903983958927683423, 904183917188438919⟩, true⟩

def words03 : List Nat := [360581893335032609, 360581892218330932, 360581891101537778, 360581890736536303, 360581889620372717, 360581887771510112, 360581885922655241, 360581884638517776, 360581883732972320, 360581883052534658]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 36430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 36400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360516944091757316, 360516952213693644⟩, ⟨2366043241905283942, 2366243370614074352⟩, true⟩

def words04 : List Nat := [360581882372067775, 360581881315466598, 360581880548162600, 360581879889395381, 360581879230534851, 360581878211979534, 360581876442680645, 360581874294995351, 360581872147339755, 360581869727290738]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 36440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 36400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360494429718064573, 360494437844617239⟩, ⟨3186957480551723937, 3187157777549427779⟩, true⟩

def words05 : List Nat := [360581867946734344, 360581866917205436, 360581865887677542, 360581864383696401, 360581862768639425, 360581860746216413, 360581858723750994, 360581857452180925, 360581855430372357, 360581853033249972]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 36450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 36400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360537416680320469, 360537424811510003⟩, ⟨1619286855548146056, 1619487321628592442⟩, true⟩

def words06 : List Nat := [360581850636149035, 360581848445594767, 360581846737391673, 360581845007938861, 360581843278548618, 360581840787437567, 360581837546296966, 360581835055787494, 360581832565266029, 360581830825264558]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 36460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 36400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569971055188486, 360569979191049156⟩, ⟨431793231869057390, 431993868329325120⟩, true⟩

def words07 : List Nat := [360581829608131185, 360581828012759180, 360581826417380570, 360581825572342569, 360581825105356102, 360581824438935989, 360581823772507578, 360581822526481521, 360581821452292155, 360581821128229237]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 36470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 36400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591594298005376, 360591602438485000⟩, ⟨(-357063183801365398), (-356862378818062484)⟩, true⟩

def words08 : List Nat := [360581821139661016, 360581821687339421, 360581821856883573, 360581822026480589, 360581822026891321, 360581822365194020, 360581822605075075, 360581822845034029, 360581822845471292, 360581822975636132]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 36480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 36400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360614379138793444, 360614387283914241⟩, ⟨(-1188720839699651293), (-1188519865337363073)⟩, true⟩

def words09 : List Nat := [360581822976041875, 360581822924492498, 360581823570061145, 360581823775367782, 360581823775824521, 360581823333569414, 360581823197767169, 360581824202775764, 360581825095313927, 360581825987913108]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 36490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 36400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 36400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk364
