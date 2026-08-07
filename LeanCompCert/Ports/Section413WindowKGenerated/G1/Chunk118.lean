import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk118

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362365147643717791, 362365149422975527⟩, ⟨1417603706508185355, 1417617915900698647⟩, true⟩

def state01 : KState := ⟨⟨362371785639378838, 362371787421772017⟩, ⟨1339605902482648867, 1339620148889265969⟩, true⟩

def words00 : List Nat := [371285276354481870, 371285273301604222, 371285267767820141, 371285263575860571, 371285259384504556, 371285253987656141, 371285239069991565, 371285231274739768, 371285223480623917, 371285218425064927]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 11800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 11800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362407822573899249, 362407824359476318⟩, ⟨913965605041654509, 913979889066415213⟩, true⟩

def words01 : List Nat := [371285208821483010, 371285199128808362, 371285189437636705, 371285186863484291, 371285181886071639, 371285177371890211, 371285172858349712, 371285167952330556, 371285155765179114, 371285149223187521]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 11810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 11800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362403856329175086, 362403858117878645⟩, ⟨960893129261018642, 960907450257031394⟩, true⟩

def words02 : List Nat := [371285143248695030, 371285143249045862, 371285136257904704, 371285127680389669, 371285119104189732, 371285110497214820, 371285098645387595, 371285093898054157, 371285089151409139, 371285084445034777]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 11820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 11800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362521666387015593, 362521668178889189⟩, ⟨(-433227126567734922), (-433212768054387194)⟩, true⟩

def words03 : List Nat := [371285077813184952, 371285078047030503, 371285085377312268, 371285085377662893, 371285084565838769, 371285082586617609, 371285080607594609, 371285080174675550, 371285079262269860, 371285082352687485]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 11830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 11800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362379015074430455, 362379016869469610⟩, ⟨1256412217448699308, 1256426613458377794⟩, true⟩

def words04 : List Nat := [371285085481143922, 371285085481494988, 371285080828858778, 371285080830119677, 371285081404969574, 371285081405320503, 371285072516739691, 371285062111717435, 371285051708307499, 371285044431786773]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 11840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 11800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362336737078779242, 362336738876981034⟩, ⟨1757702567376823438, 1757717000879711302⟩, true⟩

def words05 : List Nat := [371285035485311042, 371285029516587002, 371285023548758297, 371285017595084433, 371285002191878451, 371284988955190308, 371284975720547333, 371284968302098916, 371284956854571730, 371284944357662292]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 11850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 11800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362390696411124897, 362390698212469029⟩, ⟨1117856982876270503, 1117871453663629395⟩, true⟩

def words06 : List Nat := [371284931862708731, 371284924512571399, 371284913643818279, 371284909838047771, 371284906032811851, 371284900818203924, 371284888452617326, 371284883146837850, 371284877841777803, 371284874409070852]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 11860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 11800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362350718185369373, 362350719989928510⟩, ⟨1592904288922454359, 1592918797887618851⟩, true⟩

def words07 : List Nat := [371284866476037254, 371284858498337688, 371284850521828795, 371284848329173447, 371284842590029753, 371284838528712934, 371284834467965513, 371284829615206963, 371284815350868284, 371284804063824775]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 11870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 11800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362381444099985301, 362381445907678515⟩, ⟨1227825735252000608, 1227840281466512000⟩, true⟩

def words08 : List Nat := [371284792778475918, 371284788140649675, 371284776842044351, 371284764504192629, 371284752168286532, 371284741991028474, 371284729357465588, 371284723761384648, 371284718166125111, 371284712541948197]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 11880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 11800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362453192984180065, 362453194795059977⟩, ⟨374114990638545977, 374129574759092433⟩, true⟩

def words09 : List Nat := [371284703857753388, 371284696827022979, 371284689797301970, 371284685747131633, 371284674523514778, 371284662480550980, 371284650439466452, 371284645424566481, 371284636896917034, 371284634255123767]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 11890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 11800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 11800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk118
