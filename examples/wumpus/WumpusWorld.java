import java.awt.*;
import javax.swing.JFrame;
import javax.swing.JPanel;

public class WumpusWorld extends JFrame {

    private final int xdim;
    private final int ydim;
    
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

    private final WPanel wp;
    
    public WumpusWorld(int xdim, int ydim) {
	
        super("Wumpus");
        
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
      
	// super.setResizable(false);
	// super.setLocation(gridCellSize, gridCellSize);
	super.setVisible(true);
        // super.setDefaultCloseOperation(EXIT_ON_CLOSE);
	wp = new WPanel(this);
	super.add(wp);
        super.pack();
        
    }

    public int getXDim() {
	return xdim;
    }

    public int getYDim() {
	return ydim;
    }
    
    public void setPit(int x, int y, boolean value) {
        if (x>0 && x<=xdim && y>0 && y<=ydim)
            pit[x-1][y-1] = value;
    }

    public boolean getPit(int x, int y) {
        if (x>0 && x<=xdim && y>0 && y<=ydim)
            return pit[x-1][y-1];
        else
            return false;
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
    
    public void moveAgent(String dir) {
	switch (dir) {
	    case "north":
		agent_y += 1;
		break;
	    case "east":
		agent_x += 1;
		break;
	    case "south":
		agent_y -= 1;
		break;
	    case "west":
		agent_x -= 1;
		break;
            default:
                break;
	}
	agent_x = (0 > agent_x ? 0 : agent_x);
	agent_y = (0 > agent_y ? 0 : agent_y);
	agent_x = (agent_x > xdim-1 ? xdim-1 : agent_x);
	agent_y = (agent_y > ydim-1 ? ydim-1 : agent_y);
        if (pit[agent_x][agent_y] ||
                wumpus_x == agent_x && wumpus_y == agent_y)
            agent_alive = false;
        repaint();
    }

    public void grabGold() {
	if (agent_x == gold_x && agent_y == gold_y && !has_gold)
	    has_gold = true;
        repaint();
    }
    
    public boolean shoot(String dir) {
        boolean result = false;
        switch (dir) {
            case "north":
                if (agent_x == wumpus_x && agent_y < wumpus_y && wumpus_alive)
                    result = true;
                break;
            case "west":
                if (agent_x > wumpus_x && agent_y == wumpus_y && wumpus_alive)
                    result = true;
                break;
            case "south":
                if (agent_x == wumpus_x && agent_y > wumpus_y && wumpus_alive)
                    result = true;
                break;
            case "east":
                if (agent_x < wumpus_x && agent_y == wumpus_y && wumpus_alive)
                    result = true;
                break;
            default:
                break;
        }
        if (result)
            wumpus_alive = false;
        return result;
    }
    
    public boolean stench() {
        return (agent_x == wumpus_x && agent_y == wumpus_y-1 ||
                agent_x == wumpus_x && agent_y == wumpus_y+1 ||
                agent_x == wumpus_x-1 && agent_y == wumpus_y ||
                agent_x == wumpus_x+1 && agent_y == wumpus_y);
    }
    
    public boolean breeze() {
        return (agent_y > 0 && pit[agent_x][agent_y-1] ||
                agent_x > 0 && pit[agent_x-1][agent_y] ||
                agent_y < ydim-1 && pit[agent_x][agent_y+1] ||
                agent_x < xdim-1 && pit[agent_x+1][agent_y]);
    }    
    
    public boolean glitter() {
        return (agent_x == gold_x && agent_y == gold_y && !has_gold);
    }
    
    class WPanel extends JPanel {
	
	WumpusWorld wumpusWorld;
	int gridCellSize = 50;
        int margin = 10;
        int cellMargin = 5;
	
        public WPanel(WumpusWorld wumpusWorld) {
            // super.setPreferredSize(new Dimension(300, 300));
            super.setPreferredSize(
                    new Dimension(
                            wumpusWorld.xdim*gridCellSize+2*margin,
                            wumpusWorld.ydim*gridCellSize+2*margin));
	    this.wumpusWorld = wumpusWorld;
            // this.gridCellSize = this.getWidth()/wumpusWorld.xdim;
        }

        @Override
        public void paintComponent(Graphics g) {
            super.paintComponent(g);

	    // grid
	    for (int i=0; i<wumpusWorld.getXDim()+1; i++)
		g.drawLine(margin+i*gridCellSize,margin,margin+i*gridCellSize,
                        margin+(wumpusWorld.getYDim())*gridCellSize);
	    for (int i=0; i<wumpusWorld.getYDim()+1; i++)
		g.drawLine(margin,margin+i*gridCellSize,
                        margin+(wumpusWorld.getXDim())*gridCellSize,
                        margin+i*gridCellSize);

	    // pits
	    for (int i=0; i<wumpusWorld.getXDim(); i++)
		for (int j=0; j<wumpusWorld.getYDim(); j++)
		    {
			int k = wumpusWorld.getYDim() - j - 1;
			if (wumpusWorld.getPit(i+1,j+1))
			    g.fillRoundRect(
					    margin+i*gridCellSize+cellMargin,
					    margin+k*gridCellSize+cellMargin,
					    gridCellSize-2*cellMargin,
					    gridCellSize-2*cellMargin,
					    margin,margin);
		    }

	    // agent
	    g.drawString("A",
                    margin+(wumpusWorld.getAgentPosX()-1)*gridCellSize+20,
                    margin+(wumpusWorld.getYDim() - wumpusWorld.getAgentPosY())*gridCellSize+20);

	    // wumpus
	    g.drawString("W",
                    margin+(wumpusWorld.getWumpusPosX()-1)*gridCellSize+7,
                    margin+(wumpusWorld.getYDim() - wumpusWorld.getWumpusPosY())*gridCellSize+20);

	    // gold
	    if (!has_gold)
		g.drawString("G",
			     margin+(wumpusWorld.getGoldPosX()-1)*gridCellSize+33,
			     margin+(wumpusWorld.getYDim() - wumpusWorld.getGoldPosY())*gridCellSize+20);	    
        }
    }

    
    public static void main(String[] args) {
        
        WumpusWorld wumpusWorld = new WumpusWorld(4,4);
	wumpusWorld.setPit(2,2,true);
		
    }
    
}
