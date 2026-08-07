import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk763

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360573664826010555, 360573702604512461⟩, ⟨645046768927848147, 646993646207951715⟩, true⟩

def state01 : KState := ⟨⟨360588329663182280, 360588367451945722⟩, ⟨(-473927090190407725), (-471979429903969925)⟩, true⟩

def words00 : List Nat := [360582182096437032, 360582182172955337, 360582182430327948, 360582182687904386, 360582182799403339, 360582182800491031, 360582182740538286, 360582182590774011, 360582182440694661, 360582182505740012]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 76300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 76300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591882187215103, 360591919986343722⟩, ⟨(-745079324846679099), (-743130873542504665)⟩, true⟩

def words01 : List Nat := [360582182506718595, 360582182486185713, 360582182467489838, 360582182611642783, 360582182712136054, 360582182812804039, 360582182827379113, 360582182828474333, 360582182945343303, 360582183074176134]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 76310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 76300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582064247623798, 360582102057015237⟩, ⟨4205516015837413, 6154750628295987⟩, true⟩

def words02 : List Nat := [360582183198629475, 360582183221253498, 360582183222229716, 360582183121129123, 360582183019855402, 360582182831895360, 360582182760103988, 360582182791763010, 360582182792749120, 360582182690457243]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 76320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 76300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599319713300298, 360599357532959086⟩, ⟨(-1313017828149851332), (-1311067809778683596)⟩, true⟩

def words03 : List Nat := [360582182788026245, 360582182886967821, 360582183156981208, 360582183255981411, 360582183257002571, 360582183193214710, 360582183143679135, 360582183245065183, 360582183470916160, 360582183697015378]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 76330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 76300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597302553941392, 360597340383971263⟩, ⟨(-1159004266086969954), (-1157053455935716142)⟩, true⟩

def words04 : List Nat := [360582183837077767, 360582184068699169, 360582184471422695, 360582184874454948, 360582185233954879, 360582185479764868, 360582185605946082, 360582185732230828, 360582185786056054, 360582185985784786]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 76340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 76300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360566108481246591, 360566146321521652⟩, ⟨1222837583776851035, 1224789176199447851⟩, true⟩

def words05 : List Nat := [360582186206779333, 360582186427970480, 360582186551198401, 360582186552286818, 360582186504327046, 360582186413484826, 360582186322309242, 360582186323397848, 360582186200121804, 360582185991194249]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 76350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 76300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593619739217751, 360593657589784908⟩, ⟨(-878115108754760269), (-876162730377962833)⟩, true⟩

def words06 : List Nat := [360582185782025740, 360582185659070475, 360582185666072006, 360582185673269389, 360582185674282880, 360582185536598130, 360582185227642948, 360582185090235304, 360582184985124241, 360582185136492717]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 76360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 76300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360573895827858300, 360573933688788089⟩, ⟨628282153757064908, 630235323579139836⟩, true⟩

def words07 : List Nat := [360582185201915731, 360582185267455881, 360582185312832791, 360582185444101651, 360582185468718303, 360582185493506041, 360582185494493044, 360582185387390177, 360582185109054278, 360582185002267785]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 76370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 76300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573189951275853, 360573227822459286⟩, ⟨682142788456954075, 684096741503686629⟩, true⟩

def words08 : List Nat := [360582184895122140, 360582184846284849, 360582184661850782, 360582184353202559, 360582184044357700, 360582183692663912, 360582183447545070, 360582183373784791, 360582183299902576, 360582183140452528]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 76380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 76300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585137977742716, 360585175859218858⟩, ⟨(-230703178068449192), (-228748438711461906)⟩, true⟩

def words09 : List Nat := [360582183024118516, 360582182902353474, 360582182784674233, 360582182785763132, 360582182620232461, 360582182287861959, 360582181955291551, 360582181765136438, 360582181768578239, 360582181808896069]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 76390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 76300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 76300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk763
