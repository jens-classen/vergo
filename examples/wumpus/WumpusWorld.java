import java.awt.*;
import javax.swing.JFrame;
import javax.swing.JPanel;

public class WumpusWorld extends JFrame {

    public enum Direction {north, east, south, west};

    private int xdim;
    private int ydim;
    
    private int agent_x;
    private int agent_y;
    private boolean agent_alive;
    
    private int wumpus_x;
    private int wumpus_y;
    private boolean wumpus_alive;
    
    private int gold_x;
    private int gold_y;
    private boolean has_gold;
    
    private boolean[][] pit;

    private WPanel wp;
    
    public WumpusWorld(int xdim, int ydim) {

        super("Wumpus");
        super.setSize(1000, 620);
	// super.setResizable(false);
	// super.setLocation(50, 50);
	super.setVisible(true);
	super.setDefaultCloseOperation(EXIT_ON_CLOSE);
	wp = new WPanel(this);
	super.add(wp);
	
	this.xdim = xdim;
	this.ydim = ydim;
	pit = new boolean[xdim][ydim];
	agent_x = 0;
	agent_y = 0;
	agent_alive = true;
	wumpus_x = xdim-1;
	wumpus_y = ydim-1;
	wumpus_alive = true;
	gold_x = 0;
	gold_y = ydim-1;
	has_gold = false;

    }

    public int getXDim() {
	return xdim;
    }

    public int getYDim() {
	return ydim;
    }
    
    public void setPit(int x, int y, boolean value) {
	pit[x-1][y-1] = value;
    }

    public boolean getPit(int x, int y) {
    	return pit[x-1][y-1];
    }

    public void setAgentPos(int x, int y) {
	agent_x = x - 1;
	agent_y = y - 1;
    }

    public int getAgentPosX() {
	return agent_x + 1;
    }

    public int getAgentPosY() {
	return agent_y + 1;
    }

    public void setWumpusPos(int x, int y) {
	wumpus_x = x - 1;
	wumpus_y = y - 1;
    }

    public int getWumpusPosX() {
	return wumpus_x + 1;
    }

    public int getWumpusPosY() {
	return wumpus_y + 1;
    }
   
    public void setGoldPos(int x, int y) {
	gold_x = x - 1;
	gold_y = y - 1;
    }

    public int getGoldPosX() {
	return gold_x + 1;
    }

    public int getGoldPosY() {
	return gold_y + 1;
    }

    public boolean agentAlive() {
	return agent_alive;
    }

    public boolean wumpusAlive() {
	return wumpus_alive;
    }
    
    public boolean hasGold() {
	return has_gold;
    }
    
    public void moveAgent(Direction dir) {
	switch (dir) {
	    case north:
		agent_y += 1;
		break;
	    case east:
		agent_x += 1;
		break;
	    case south:
		agent_y -= 1;
		break;
	    case west:
		agent_x -= 1;
		break;
	}
	agent_x = (0 > agent_x ? 0 : agent_x);
	agent_y = (0 > agent_y ? 0 : agent_y);
	agent_x = (agent_x > xdim-1 ? xdim-1 : agent_x);
	agent_y = (agent_y > ydim-1 ? ydim-1 : agent_y);
    }

    public void grabGold() {
	if (agent_x == gold_x && agent_y == gold_y && !has_gold)
	    has_gold = true;
    }
    

    class WPanel extends JPanel {
	
	WumpusWorld wumpusWorld;
	int gridCellSize = 50;
	
        public WPanel(WumpusWorld wumpusWorld) {
            super.setPreferredSize(new Dimension(300, 300));
	    this.wumpusWorld = wumpusWorld;
        }

        @Override
        public void paintComponent(Graphics g) {
            super.paintComponent(g);

	    // grid
	    for (int i=0; i<wumpusWorld.getXDim()+1; i++)
		g.drawLine(10+i*50,10,10+i*50,10+(wumpusWorld.getYDim())*50);
	    for (int i=0; i<wumpusWorld.getYDim()+1; i++)
		g.drawLine(10,10+i*50,10+(wumpusWorld.getXDim())*50,10+i*50);

	    // pits
	    for (int i=0; i<wumpusWorld.getXDim(); i++)
		for (int j=0; j<wumpusWorld.getYDim(); j++)
		    if (wumpusWorld.getPit(i+1,j+1))
			g.fillRoundRect(10+i*50+5,10+j*50+5,40,40,10,10);

	    // agent
	    g.drawString("A",10+(wumpusWorld.getAgentPosX()-1)*50+20,10+(wumpusWorld.getAgentPosY()-1)*50+20);

	    // wumpus
	    g.drawString("W",10+(wumpusWorld.getWumpusPosX()-1)*50+20,10+(wumpusWorld.getWumpusPosY()-1)*50+20);

	    // gold
	    g.drawString("G",10+(wumpusWorld.getGoldPosX()-1)*50+20,10+(wumpusWorld.getGoldPosY()-1)*50+20);	    
        }
    }

    
    public static void main(String[] args) {
        
        WumpusWorld wumpusWorld = new WumpusWorld(4,4);
	wumpusWorld.setPit(2,2,true);
		
    }
    
}
