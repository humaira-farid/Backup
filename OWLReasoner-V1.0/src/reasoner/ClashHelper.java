package reasoner;

import javax.annotation.Nonnull;

public enum ClashHelper {
    /** operations */                                       CLASH           ("there is clash"),
    /** operations */                                       NOCLASH           ("No clash"),
    /** operations */                                       HANDLED    ("clash is handled");
	
	@Nonnull private final String name;
	private ClashHelper(String s) {
        name = s;
    }
}
