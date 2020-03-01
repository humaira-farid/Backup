package reasoner.todolist;

import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

public class ToDoEntryComparator implements Comparator<ToDoEntry>{
	 private List<Comparator<ToDoEntry>> listComparators;
	 
	    @SafeVarargs
	    public ToDoEntryComparator(Comparator<ToDoEntry>... comparators) {
	        this.listComparators = Arrays.asList(comparators);
	    }
	@Override
	public int compare(ToDoEntry e1, ToDoEntry e2) {
		for (Comparator<ToDoEntry> comparator : listComparators) {
            int result = comparator.compare(e1, e2);
            if (result != 0) {
                return result;
            }
        }
        return 0;
	}

}
