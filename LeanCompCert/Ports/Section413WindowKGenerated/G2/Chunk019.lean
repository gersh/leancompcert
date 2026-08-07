import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk019

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360266178482053487, 360266178498404387⟩, ⟨563670228700388232, 563670249851040308⟩, true⟩

def state01 : KState := ⟨⟨360974054642748352, 360974054659280795⟩, ⟨(-783880860832311117), (-783880839335804099)⟩, true⟩

def words00 : List Nat := [360562805964967417, 360563061922975675, 360563338748886502, 360563615284170323, 360563653421273510, 360563653421292769, 360563470750630701, 360563514174055405, 360563645842854696, 360563860604160019]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 1900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 1900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361248897268028294, 361248897284745068⟩, ⟨(-1310586035482732398), (-1310586013633234594)⟩, true⟩

def words01 : List Nat := [360563860604177595, 360563853226465313, 360564106194345530, 360564593435378368, 360565002401863364, 360565410941678070, 360565663127903379, 360565944698134535, 360566300402622482, 360566655736783989]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 1910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 1900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360662579902443919, 360662579919343724⟩, ⟨(-183269115889105311), (-183269093687254753)⟩, true⟩

def words02 : List Nat := [360567076653765670, 360567329281330124, 360567443522415177, 360567557644810414, 360567557644827102, 360567437582182744, 360567544523214273, 360567651353372282, 360567651353389647, 360567671015310967]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 1920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 1900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361181066475852614, 361181066492937035⟩, ⟨(-1185242723970261558), (-1185242701411190816)⟩, true⟩

def words03 : List Nat := [360567981715124072, 360568292093474068, 360568863461850919, 360569178072211954, 360569259064747770, 360569339973658318, 360569469435652968, 360569801561796393, 360570116646828581, 360570431407202264]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 1930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 1900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361020109894474879, 361020109911746363⟩, ⟨(-877738741467898996), (-877738718544975202)⟩, true⟩

def words04 : List Nat := [360570612566357413, 360570612566377019, 360570554187358424, 360570569796070631, 360570569796087111, 360570513602310532, 360570483368667687, 360570232378544557, 360569987491957263, 360570218205675131]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 1940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 1900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360118454579303152, 360118454596761137⟩, ⟨886472247873290800, 886472271160839516⟩, true⟩

def words05 : List Nat := [360570704748462505, 360571190793001886, 360571476994117734, 360571510976285007, 360571510976301654, 360571337396809296, 360571163994704818, 360571067956068701, 360570967241539114, 360570736367761566]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 1950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 1900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨359881647390032062, 359881647407678063⟩, ⟨1353154273811311349, 1353154297468331035⟩, true⟩

def words06 : List Nat := [360570505729444735, 360570367396837324, 360570406500717488, 360570451718704648, 360570451718723015, 360570269288779483, 360569838133562502, 360569393500552694, 360568949319170670, 360568527761722902]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 1960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 1900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360465337081778268, 360465337099615269⟩, ⟨199511277684782317, 199511301718999127⟩, true⟩

def words07 : List Nat := [360568179268410615, 360567693454994513, 360567208134036298, 360566972916524593, 360566940351699460, 360566819423937118, 360566698618507138, 360566450684231657, 360566151299551272, 360566100383311734]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 1970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 1900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360084711488538288, 360084711506564920⟩, ⟨952573424403354849, 952573448814017435⟩, true⟩

def words08 : List Nat := [360566049518470311, 360565986702761280, 360565679102960257, 360565246073556561, 360564813480451321, 360564311145752188, 360563943612244379, 360563822250533955, 360563701010854223, 360563391631597090]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 1980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 1900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360990549967858940, 360990549986076680⟩, ⟨(-857762759828975768), (-857762735037039664)⟩, true⟩

def words09 : List Nat := [360563151209652237, 360562935533329406, 360562749176974888, 360562749176995086, 360562536631845753, 360562103759501131, 360561671320675371, 360561482805215665, 360561668618537169, 360561882952075161]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 1990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 1900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 1900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk019
