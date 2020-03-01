package reasoner.todolist;

import java.util.Comparator;

public class ToDoEntryIDComparator implements Comparator<ToDoEntry>{

	@Override
	public int compare(ToDoEntry e1, ToDoEntry e2) {
		return e1.getNode().getId() - e2.getNode().getId();
	}

}
