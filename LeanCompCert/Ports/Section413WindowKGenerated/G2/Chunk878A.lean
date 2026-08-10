import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk878A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598138060987374, 360598188635397882⟩, ⟨(-1411865470475329764), (-1408866847703623062)⟩, true⟩

def state01 : KState := ⟨⟨360603506220877817, 360603556807347642⟩, ⟨(-1883289701038534596), (-1880290019399383168)⟩, true⟩

def words00 : List Nat := [360582142573375504, 360582142692508112, 360582142940952712, 360582143189777645, 360582143362328001, 360582143453352663, 360582143479292964, 360582143505393149, 360582143640896536, 360582143886194263]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 87800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 87800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590971705031364, 360591022303401214⟩, ⟨(-782526190387836459), (-779525463746928045)⟩, true⟩

def words01 : List Nat := [360582144260614193, 360582144635269191, 360582144911417590, 360582145145934676, 360582145271631489, 360582145397637334, 360582145626709267, 360582145799709798, 360582145901912650, 360582146004295682]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 87810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 87800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360606827259826445, 360606877870155898⟩, ⟨(-2174980687376105098), (-2171978910385899632)⟩, true⟩

def words02 : List Nat := [360582146197207399, 360582146517290023, 360582146916211295, 360582147315373779, 360582147603747230, 360582147762719253, 360582148015298984, 360582148268251060, 360582148517709279, 360582148800574704]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 87820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 87800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599359483779723, 360599410106159919⟩, ⟨(-1519022842669928370), (-1516020007202469456)⟩, true⟩

def words03 : List Nat := [360582149017280996, 360582149234108789, 360582149580161552, 360582149991746512, 360582150318616514, 360582150645700375, 360582150873454022, 360582151027331224, 360582151224839596, 360582151422775139]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 87830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 87800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596008127525804, 360596058761834476⟩, ⟨(-1224711359236921690), (-1221707475913652346)⟩, true⟩

def words04 : List Nat := [360582151609155622, 360582151695582161, 360582151696729286, 360582151677793481, 360582151658651710, 360582151652507606, 360582151801108602, 360582151949948873, 360582152016323749, 360582152175957097]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 87840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 87800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk878A
