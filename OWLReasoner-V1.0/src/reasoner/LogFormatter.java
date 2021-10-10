package reasoner;

import java.util.logging.Formatter;
import java.util.logging.LogRecord;

public class LogFormatter extends Formatter {
	@Override
	public String format(LogRecord record) {
		StringBuffer sb = new StringBuffer();
        sb.append(record.getLevel());
        sb.append(": ");
        sb.append(record.getMessage());
        sb.append("\n");
        return sb.toString();
	}
}
