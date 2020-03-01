package reasoner.todolist;

import java.util.Comparator;

public class ToDoEntryTypeComparator implements Comparator<ToDoEntry>{
	 
	@Override
	public int compare(ToDoEntry e1, ToDoEntry e2) {
		return e1.getTypeValue().compareTo(e1.getTypeValue());
	}

}
